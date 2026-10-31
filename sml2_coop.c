/*
 * sml2_coop.c — local simultaneous co-op for Super Mario Land 2.
 *
 * Player 1 is the body in Mario's registers. Player 2 is a second body
 * whose position this file integrates: gravity, the level block map, and
 * his own buttons. Once a frame, from inside the ROM dispatch,
 * 00:1413, 00:1BFF and 00:2D7D run on his position for coins, blocks
 * and enemies. Each call is one instruction at a time and ignores the
 * end-of-frame stop flag, which was aborting the routine immediately.
 * What happened is appended to sml2-coop.log beside the executable.
 * Actor AI still runs once.
 *
 * His walk is not Mario's 00:0F71: that routine was dragging the camera.
 * Pipes stay on player 1.
 *
 * Lives ($A22C), coins, the timer and the camera stay shared. One player
 * falling only takes him out; the wipe still belongs to the ROM.
 */
#include "sml2_coop.h"
#include "sml2_mods.h"
#include "sml2_map.h"
#include "gb_body.h"
#include "gb_custom_view.h"
#include "gbrt.h"
#include "ppu.h"
#include "game_extras.h"
#include "gb_host_paths.h"
#include <SDL.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MODE_PLAY 0x04
#define MODE_DEAD 0x09
#define KEY_A      0x01
#define KEY_B      0x02
#define KEY_RIGHT  0x10
#define KEY_LEFT   0x20
#define KEY_UP     0x40
#define KEY_DOWN   0x80
#define HUD_Y      136
/* Speeds are 8.8 fixed point. One pixel is PX. */
#define PX         256
/* The stored Y is Mario's origin. His floor sample is 28 px below that
 * (00:1E3B). The square is 16 px, so its top sits 12 px under the origin
 * and its bottom on that sample. */
#define SQUARE_H   16
#define SQUARE_TOP 12
#define DRAW_DROP  5
#define PC_BLOCKS  0x1413u
#define PC_BODY    0x1BFFu

/* Return sites of the three ROM calls this mod wraps. Same addresses on
 * the faithful body and on DX. */
#define PC_AFTER_MOVE 0x060Fu
#define PC_AFTER_HIT  0x0626u
#define PC_AFTER_DEAD 0x0643u
#define PC_MOVE       0x0F71u
#define PC_CLAMP      0x0FBFu
#define PC_HIT        0x2D7Du
#define PC_SHOT_A     0x324Fu
#define PC_SHOT_B     0x331Cu

#define PHASE_IDLE 0
#define PHASE_MOVE 1
#define PHASE_HIT  2

#define BLOB_MAX 96
#define RESPAWN_FRAMES 120

typedef struct {
    uint16_t af, bc, de, hl;
    uint8_t fz, fn, fh, fc;
} Regs;

typedef struct {
    uint8_t eram[BLOB_MAX];
    uint8_t pos[4]; /* $FFC0..$FFC3, little-endian Y then X */
    int x, y;
    int fx, fy;     /* 8.8 position, so speeds below one pixel still add up */
    int vx, vy;
    int grounded;
    int alive;
    int hide;
    int respawn;
    int face; /* 1 right, 0 left. His own, not Mario's. */
    int anim;
} Player;

static Player s_pl[2];
static int s_lead;          /* who currently occupies Mario's registers */
static int s_phase;
static int s_pumping;
static int s_pump_steps;
static uint16_t s_pump_pc;
static int s_hit_frames;
static FILE *s_log;
static int s_lock_p2;       /* the body in the registers is reading player 2 */
static int s_on;
static int s_in_pipe;
static int s_level = -1;
static int s_prev_mode = -1;
static int s_track_x = -1;
static int s_track_y = -1;
static int s_blob_n;
static uint16_t s_addr[BLOB_MAX];
static Regs s_regs;
static uint8_t s_saved_held, s_saved_pressed;
static int s_mode_before;
static uint8_t s_held, s_pressed, s_prev_held;
static uint64_t s_polled_frame;
static SDL_GameController *s_pad2;
/* Launcher Player 2 card: 0 none, 1 keyboard, 2 one gamepad. */
static int s_p2_src = 1;
static char s_p2_guid[40];
static int s_p2_slot;
enum { P2N = 8 };
static int s_p2_key[P2N][2];
static const uint8_t s_p2_bit[P2N] = {
    KEY_UP, KEY_DOWN, KEY_LEFT, KEY_RIGHT, KEY_A, KEY_B, 0x08, 0x04
};
static const char *s_p2_name[P2N] = {
    "up", "down", "left", "right", "a", "b", "start", "select"
};

static GBDispatchFn s_real_dispatch;
static GBDispatchFn s_real_dispatch_call;
static GBCustomRender s_prev_render;
static GBCustomSnapshot s_prev_snapshot;
static GBCustomSnapshot s_prev_reset;
static GBCustomReadOverride s_prev_override;

static uint8_t eram_at(const GBContext *ctx, unsigned addr) {
    if (!ctx->eram || addr < 0xA000u || addr >= 0xC000u) return 0;
    unsigned off = (unsigned)ctx->ram_bank * 0x2000u + (addr - 0xA000u);
    return off < ctx->eram_size ? ctx->eram[off] : 0;
}

static void eram_put(GBContext *ctx, unsigned addr, uint8_t value) {
    if (!ctx->eram || addr < 0xA000u || addr >= 0xC000u) return;
    unsigned off = (unsigned)ctx->ram_bank * 0x2000u + (addr - 0xA000u);
    if (off < ctx->eram_size) ctx->eram[off] = value;
}

static int hram16(const GBContext *ctx, unsigned addr) {
    unsigned i = addr - 0xFF80u;
    if (!ctx->hram || i + 1 >= 0x7F) return 0;
    return ctx->hram[i] | (ctx->hram[i + 1] << 8);
}

static int mode_of(const GBContext *ctx) {
    return ctx->hram ? ctx->hram[0x9B - 0x80] : 0;
}

static void mode_set(GBContext *ctx, int mode) {
    if (ctx->hram) ctx->hram[0x9B - 0x80] = (uint8_t)mode;
}

static int piping(const GBContext *ctx) {
    return eram_at(ctx, 0xA221) >= 0x10 || eram_at(ctx, 0xA20E) != 0;
}

static int ghost_index(void) { return 1 - s_lead; }

static void bind_addrs(void) {
    int n = 0;
    /* Mario's working RAM, minus the shared life counter at $A22C.
     * $A24E is the bank-switch scratch and stays out too (the range
     * stops at $A24D). Coins, the timer and the level id sit above. */
    for (unsigned a = 0xA200; a <= 0xA24D; a++) {
        if (a == 0xA22C) continue;
        s_addr[n++] = (uint16_t)a;
    }
    static const uint16_t extra[] = {
        0xA24F, 0xA266, 0xA267, 0xA268, 0xA271, 0xA272,
        0xA279, 0xA27A, 0xA284, 0xA291, 0xA299, 0xA2DC, 0xA2DE
    };
    for (unsigned i = 0; i < sizeof extra / sizeof extra[0]; i++)
        s_addr[n++] = extra[i];
    s_blob_n = n;
}

static void blob_set(Player *p, unsigned addr, uint8_t value) {
    for (int i = 0; i < s_blob_n; i++) {
        if (s_addr[i] == addr) { p->eram[i] = value; return; }
    }
}

static uint8_t blob_get(const Player *p, unsigned addr) {
    for (int i = 0; i < s_blob_n; i++) {
        if (s_addr[i] == addr) return p->eram[i];
    }
    return 0;
}

static void note_pos(Player *p) {
    int y = p->pos[0] | (p->pos[1] << 8);
    int x = p->pos[2] | (p->pos[3] << 8);
    /* Keep the sub-pixel if the pixel itself did not change. */
    if (x != p->x) p->fx = x * PX;
    if (y != p->y) p->fy = y * PX;
    p->x = x;
    p->y = y;
}

static void set_pos(Player *p, int x, int y) {
    if (x < 0) x = 0;
    if (y < 0) y = 0;
    p->pos[0] = (uint8_t)y;
    p->pos[1] = (uint8_t)(y >> 8);
    p->pos[2] = (uint8_t)x;
    p->pos[3] = (uint8_t)(x >> 8);
    note_pos(p);
    p->fx = p->x * PX;
    p->fy = p->y * PX;
    blob_set(p, 0xA229, p->pos[0]);
    blob_set(p, 0xA22A, p->pos[1]);
    blob_set(p, 0xA227, p->pos[2]);
    blob_set(p, 0xA228, p->pos[3]);
}

/* Neutral physics plus a short mercy window, so a respawn does not
 * inherit a pipe ride or a death bounce. */
static void set_idle(Player *p) {
    p->vx = 0;
    p->vy = 0;
    p->grounded = 1;
    blob_set(p, 0xA200, 0x80);
    blob_set(p, 0xA201, 0x18);
    blob_set(p, 0xA20E, 0);
    blob_set(p, 0xA214, 0xFF);
    blob_set(p, 0xA215, 0);
    blob_set(p, 0xA217, 0x40);
    blob_set(p, 0xA221, 0);
    blob_set(p, 0xA224, 0);
    p->face = 1;
}

/* Level cells. Rows 0..15 are cart RAM bank 0, 16..31 are WRAM bank 0,
 * 32..47 are WRAM bank 1. 00:1E3B treats a block id below $48 as floor. */
static uint8_t level_byte(const GBContext *ctx, unsigned addr) {
    if (addr >= 0xD000u && addr < 0xE000u) {
        if (!ctx->wram) return 0;
        return ctx->wram[0x1000u + (addr - 0xD000u)];
    }
    if (addr >= 0xC000u && addr < 0xD000u)
        return ctx->wram ? ctx->wram[addr - 0xC000u] : 0;
    if (addr >= 0xA000u && addr < 0xC000u) {
        unsigned off = addr - 0xA000u;
        return ctx->eram && off < ctx->eram_size ? ctx->eram[off] : 0;
    }
    return 0;
}

static int occupied(const GBContext *ctx, int x, int y) {
    if (x < 0 || x >= 4096) return 1;
    if (y < 0 || y >= 768) return 0;
    unsigned addr = 0xB000u + ((unsigned)(y >> 4) & 0xFFu) * 0x100u
                            + ((unsigned)(x >> 4) & 0xFFu);
    return level_byte(ctx, addr) < 0x48;
}

/* The picture is centred on x, so the feet samples sit under the square
 * rather than on Mario's probes, which are eight pixels to its right. */
static int on_floor(const GBContext *ctx, int x, int y) {
    int feet = y + SQUARE_TOP + SQUARE_H;
    return occupied(ctx, x - 4, feet) || occupied(ctx, x + 4, feet);
}

static void publish_pos(Player *p) {
    int x = p->fx >> 8;
    int y = p->fy >> 8;
    if (x < 0) { x = 0; p->fx = 0; }
    if (y < 0) { y = 0; p->fy = 0; }
    p->x = x;
    p->y = y;
    p->pos[0] = (uint8_t)y;
    p->pos[1] = (uint8_t)(y >> 8);
    p->pos[2] = (uint8_t)x;
    p->pos[3] = (uint8_t)(x >> 8);
    blob_set(p, 0xA229, p->pos[0]);
    blob_set(p, 0xA22A, p->pos[1]);
    blob_set(p, 0xA227, p->pos[2]);
    blob_set(p, 0xA228, p->pos[3]);
}

/* One frame of player 2. He is not in Mario's registers, so this is what
 * makes the green square fall, stand and jump. */
static void step_p2(GBContext *ctx) {
    if (s_lead != 0 || s_in_pipe) return;
    Player *p = &s_pl[1];
    if (!p->alive || p->hide || (p->x | p->y) == 0) return;

    int cap = (s_held & KEY_B) ? (2 * PX + PX / 2) : (PX + PX / 2);
    int target = 0;
    if (s_held & KEY_RIGHT) target = cap;
    else if (s_held & KEY_LEFT) target = -cap;
    if (p->vx < target) p->vx += 80;
    if (p->vx > target) p->vx -= 80;
    if (p->vx > cap) p->vx = cap;
    if (p->vx < -cap) p->vx = -cap;
    if (target == 0 && p->vx > -40 && p->vx < 40) p->vx = 0;

    if (p->grounded && (s_pressed & KEY_A)) {
        p->vy = -5 * PX;
        p->grounded = 0;
    } else if (!p->grounded) {
        if (p->vy < 0 && !(s_held & KEY_A) && p->vy < -2 * PX)
            p->vy = -2 * PX;
        p->vy += 48;
        if (p->vy > 4 * PX) p->vy = 4 * PX;
    }

    p->fx += p->vx;
    {
        int nx = p->fx >> 8;
        /* First pixel past the drawn edge. The old probes sat to the right. */
        int edge = p->vx >= 0 ? nx + 8 : nx - 9;
        int mid = p->y + SQUARE_TOP + 4;
        int low = p->y + SQUARE_TOP + 12;
        if (occupied(ctx, edge, mid) || occupied(ctx, edge, low)) {
            p->fx = p->x * PX;
            p->vx = 0;
        }
    }

    {
        int x = p->fx >> 8;
        int prev = p->y;
        p->fy += p->vy;
        int ny = p->fy >> 8;
        if (p->vy >= 0) {
            if (on_floor(ctx, x, ny)) {
                int guard = 0;
                while (ny > 0 && on_floor(ctx, x, ny) && guard++ < 32) ny--;
                p->fy = ny * PX;
                p->vy = 0;
                p->grounded = 1;
            } else if (on_floor(ctx, x, ny + 1)) {
                p->fy = ny * PX;
                p->vy = 0;
                p->grounded = 1;
            } else {
                p->grounded = 0;
            }
        } else if (occupied(ctx, x - 4, ny + SQUARE_TOP) ||
                   occupied(ctx, x + 4, ny + SQUARE_TOP)) {
            p->fy = prev * PX;
            p->vy = 0;
            p->grounded = 0;
        } else {
            p->grounded = 0;
        }
    }

    publish_pos(p);
    if (s_held & KEY_LEFT) p->face = 0;
    else if (s_held & KEY_RIGHT) p->face = 1;
    if (p->grounded && p->vx) p->anim++;
    if (p->y > 740) {
        p->alive = 0;
        p->hide = 0;
        p->respawn = RESPAWN_FRAMES;
        p->vx = p->vy = 0;
        p->grounded = 0;
        return;
    }

    uint8_t mercy = blob_get(p, 0xA217);
    if (mercy) blob_set(p, 0xA217, (uint8_t)(mercy - 1));
    /* 00:2D7D stomps only while the vertical index is below $18 (falling).
     * $18 is the idle index, above that is a rise. */
    if (p->grounded) blob_set(p, 0xA201, 0x18);
    else if (p->vy > 0) blob_set(p, 0xA201, 0x10);
    else blob_set(p, 0xA201, 0x40);
    blob_set(p, 0xA214, p->grounded ? 0xFF : 0x00);
}

static void save_player(GBContext *ctx, Player *p) {
    if (!ctx->hram) return;
    memcpy(p->pos, ctx->hram + (0xFFC0 - 0xFF80), 4);
    for (int i = 0; i < s_blob_n; i++) p->eram[i] = eram_at(ctx, s_addr[i]);
    note_pos(p);
}

static void load_player(GBContext *ctx, const Player *p) {
    if (!ctx->hram) return;
    memcpy(ctx->hram + (0xFFC0 - 0xFF80), p->pos, 4);
    for (int i = 0; i < s_blob_n; i++) eram_put(ctx, s_addr[i], p->eram[i]);
}

static void save_regs(const GBContext *ctx) {
    s_regs.af = ctx->af; s_regs.bc = ctx->bc;
    s_regs.de = ctx->de; s_regs.hl = ctx->hl;
    s_regs.fz = ctx->f_z; s_regs.fn = ctx->f_n;
    s_regs.fh = ctx->f_h; s_regs.fc = ctx->f_c;
}

static void load_regs(GBContext *ctx) {
    ctx->af = s_regs.af; ctx->bc = s_regs.bc;
    ctx->de = s_regs.de; ctx->hl = s_regs.hl;
    ctx->f_z = s_regs.fz; ctx->f_n = s_regs.fn;
    ctx->f_h = s_regs.fh; ctx->f_c = s_regs.fc;
}

/* 00:2D7D overlaps enemies in screen space. Put that point on the
 * middle of the square, not on Mario's sprite anchor. */
static void write_screen(GBContext *ctx) {
    int cam_x = hram16(ctx, SML2_CAM_X);
    int cam_y = hram16(ctx, SML2_CAM_Y);
    int x = hram16(ctx, SML2_MARIO_X);
    int y = hram16(ctx, SML2_MARIO_Y);
    int sx = x - cam_x + SML2_CAM_CENTRE_X;
    int sy = y + SQUARE_TOP + SQUARE_H / 2 - cam_y + SML2_CAM_CENTRE_Y;
    eram_put(ctx, 0xA23C, (uint8_t)sx);
    eram_put(ctx, 0xA23B, (uint8_t)sy);
}

/* Mario's block probes sit about eight pixels right of his origin.
 * Shift the origin so those probes land on the square. */
static void bias_x(GBContext *ctx, int delta) {
    int x = hram16(ctx, SML2_MARIO_X) + delta;
    if (x < 0) x = 0;
    ctx->hram[SML2_MARIO_X - 0xFF80] = (uint8_t)x;
    ctx->hram[SML2_MARIO_X - 0xFF80 + 1] = (uint8_t)(x >> 8);
}

static void remember_keys(GBContext *ctx) {
    s_saved_held = ctx->hram[0xFF80 - 0xFF80];
    s_saved_pressed = ctx->hram[0xFF81 - 0xFF80];
}

static void restore_keys(GBContext *ctx) {
    ctx->hram[0] = s_saved_held;
    ctx->hram[1] = s_saved_pressed;
}

static void p2_defaults(void) {
    s_p2_src = 1;
    s_p2_guid[0] = '\0';
    s_p2_slot = 0;
    memset(s_p2_key, 0, sizeof s_p2_key);
    s_p2_key[0][0] = SDL_SCANCODE_I;
    s_p2_key[1][0] = SDL_SCANCODE_K;
    s_p2_key[2][0] = SDL_SCANCODE_J;
    s_p2_key[3][0] = SDL_SCANCODE_L;
    s_p2_key[4][0] = SDL_SCANCODE_U;
    s_p2_key[5][0] = SDL_SCANCODE_O;
    s_p2_key[6][0] = SDL_SCANCODE_P;
    s_p2_key[7][0] = SDL_SCANCODE_LEFTBRACKET;
}

static int p2_key_value(const char *val) {
    while (*val == ' ' || *val == '\t') val++;
    if (strncmp(val, "key:", 4) == 0) return atoi(val + 4);
    if (strncmp(val, "none", 4) == 0) return 0;
    return atoi(val);
}

/* Same runtime_prefs.ini the launcher writes: input.p2.src, input.p2.guid
 * and input.p2.<action> / input.p2.<action>.1. Missing lines keep the
 * defaults above. */
static void load_p2_input(void) {
    p2_defaults();
    char path[1024];
    gb_host_state_path("runtime_prefs.ini", path, sizeof path);
    FILE *f = fopen(path, "r");
    if (!f) return;
    char line[256];
    char p1_guid[40];
    int p1_src = 1, p1_slot = 0;
    p1_guid[0] = '\0';
    while (fgets(line, sizeof line, f)) {
        char *s = line;
        while (*s == ' ' || *s == '\t') s++;
        if (*s == '#' || *s == ';') continue;
        char *eq = strchr(s, '=');
        if (!eq) continue;
        *eq = '\0';
        char *key = s;
        char *val = eq + 1;
        size_t kl = strlen(key);
        while (kl && (key[kl - 1] == ' ' || key[kl - 1] == '\t')) key[--kl] = '\0';
        while (*val == ' ' || *val == '\t') val++;
        size_t vl = strlen(val);
        while (vl && (val[vl - 1] == '\n' || val[vl - 1] == '\r' ||
                      val[vl - 1] == ' ' || val[vl - 1] == '\t'))
            val[--vl] = '\0';
        if (strcmp(key, "input.p2.src") == 0) {
            int v = atoi(val);
            if (v >= 0 && v <= 2) s_p2_src = v;
            continue;
        }
        if (strcmp(key, "input.p2.guid") == 0) {
            snprintf(s_p2_guid, sizeof s_p2_guid, "%s", val);
            continue;
        }
        if (strcmp(key, "input.p2.slot") == 0) {
            int v = atoi(val);
            if (v >= 0 && v < 8) s_p2_slot = v;
            continue;
        }
        if (strcmp(key, "input.p1.src") == 0) {
            int v = atoi(val);
            if (v >= 0 && v <= 2) p1_src = v;
            continue;
        }
        if (strcmp(key, "input.p1.guid") == 0) {
            snprintf(p1_guid, sizeof p1_guid, "%s", val);
            continue;
        }
        if (strcmp(key, "input.p1.slot") == 0) {
            int v = atoi(val);
            if (v >= 0 && v < 8) p1_slot = v;
            continue;
        }
        if (strncmp(key, "input.p2.", 9) != 0) continue;
        const char *rest = key + 9;
        for (int b = 0; b < P2N; b++) {
            size_t n = strlen(s_p2_name[b]);
            if (strncmp(rest, s_p2_name[b], n) != 0) continue;
            if (rest[n] == '\0') {
                s_p2_key[b][0] = p2_key_value(val);
                break;
            }
            if (rest[n] == '.' && rest[n + 1] == '1' && rest[n + 2] == '\0') {
                s_p2_key[b][1] = p2_key_value(val);
                break;
            }
        }
    }
    fclose(f);
    /* The launcher stored both players on the first of two identical pads.
     * Player 2 takes the next one, so his jump is not Mario's button. */
    if (s_p2_src == 2 && p1_src == 2 && p1_guid[0] && s_p2_guid[0] &&
        p1_slot == s_p2_slot) {
        int same = 1;
        for (int i = 0; p1_guid[i] && s_p2_guid[i]; i++) {
            char a = p1_guid[i], b = s_p2_guid[i];
            if (a >= 'A' && a <= 'Z') a = (char)(a - 'A' + 'a');
            if (b >= 'A' && b <= 'Z') b = (char)(b - 'A' + 'a');
            if (a != b) { same = 0; break; }
        }
        if (same && s_p2_slot < 7) s_p2_slot++;
    }
}

static int pad_guid_matches(int index) {
    if (!s_p2_guid[0]) return 1;
    SDL_JoystickGUID id = SDL_JoystickGetDeviceGUID(index);
    char text[40];
    SDL_JoystickGetGUIDString(id, text, (int)sizeof text);
    for (int i = 0; text[i] && s_p2_guid[i]; i++) {
        char a = text[i], b = s_p2_guid[i];
        if (a >= 'A' && a <= 'Z') a = (char)(a - 'A' + 'a');
        if (b >= 'A' && b <= 'Z') b = (char)(b - 'A' + 'a');
        if (a != b) return 0;
        if (i == 38) return 1;
    }
    return strcmp(text, s_p2_guid) == 0;
}

static SDL_Joystick *s_joy2;

static void open_pad2(void) {
    if (s_p2_src != 2 || s_pad2 || s_joy2) return;
    SDL_JoystickUpdate();
    int n = SDL_NumJoysticks();
    int any_pad = -1;
    int any_joy = -1;
    int matches[8];
    int match_n = 0;
    for (int i = 0; i < n; i++) {
        if (SDL_IsGameController(i)) {
            if (any_pad < 0) any_pad = i;
            if (!pad_guid_matches(i)) continue;
            if (match_n < 8) matches[match_n++] = i;
        } else if (any_joy < 0) {
            any_joy = i;
        }
    }
    if (match_n > 0) {
        int pick = s_p2_slot;
        if (pick < 0 || pick >= match_n) pick = 0;
        s_pad2 = SDL_GameControllerOpen(matches[pick]);
        if (s_pad2) return;
    }
    /* No guid match. Player 1 on the keyboard leaves the plugged pad free. */
    if (!s_p2_guid[0] && any_pad >= 0) {
        s_pad2 = SDL_GameControllerOpen(any_pad);
        if (s_pad2) return;
    }
    if (!s_p2_guid[0] && any_joy >= 0) s_joy2 = SDL_JoystickOpen(any_joy);
}

static void held_from_axes(uint8_t *held, int ax, int ay) {
    if (ax > 8000) *held |= KEY_RIGHT;
    if (ax < -8000) *held |= KEY_LEFT;
    if (ay < -8000) *held |= KEY_UP;
    if (ay > 8000) *held |= KEY_DOWN;
}

static uint8_t poll_p2(void) {
    if (s_p2_src == 0) return 0;
    SDL_GameControllerUpdate();
    SDL_JoystickUpdate();
    if (s_p2_src == 2 && !s_pad2 && !s_joy2) open_pad2();
    uint8_t held = 0;
    if (s_p2_src == 1) {
        const uint8_t *keys = SDL_GetKeyboardState(NULL);
        if (keys) {
            for (int b = 0; b < P2N; b++) {
                if ((s_p2_key[b][0] > 0 && keys[s_p2_key[b][0]]) ||
                    (s_p2_key[b][1] > 0 && keys[s_p2_key[b][1]]))
                    held |= s_p2_bit[b];
            }
        }
    }
    if (s_p2_src == 2 && s_pad2 && SDL_GameControllerGetAttached(s_pad2)) {
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_DPAD_RIGHT) ||
            SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTX) > 16000)
            held |= KEY_RIGHT;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_DPAD_LEFT) ||
            SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTX) < -16000)
            held |= KEY_LEFT;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_DPAD_UP) ||
            SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTY) < -16000)
            held |= KEY_UP;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_DPAD_DOWN) ||
            SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTY) > 16000)
            held |= KEY_DOWN;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_A)) held |= KEY_A;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_B) ||
            SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_X))
            held |= KEY_B;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_START)) held |= 0x08;
        if (SDL_GameControllerGetButton(s_pad2, SDL_CONTROLLER_BUTTON_BACK)) held |= 0x04;
        held_from_axes(&held,
                       SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTX),
                       SDL_GameControllerGetAxis(s_pad2, SDL_CONTROLLER_AXIS_LEFTY));
    } else if (s_p2_src == 2 && s_joy2 && SDL_JoystickGetAttached(s_joy2)) {
        held_from_axes(&held,
                       SDL_JoystickGetAxis(s_joy2, 0),
                       SDL_JoystickGetAxis(s_joy2, 1));
        if (SDL_JoystickNumHats(s_joy2) > 0) {
            Uint8 hat = SDL_JoystickGetHat(s_joy2, 0);
            if (hat & SDL_HAT_RIGHT) held |= KEY_RIGHT;
            if (hat & SDL_HAT_LEFT) held |= KEY_LEFT;
            if (hat & SDL_HAT_UP) held |= KEY_UP;
            if (hat & SDL_HAT_DOWN) held |= KEY_DOWN;
        }
        if (SDL_JoystickGetButton(s_joy2, 0)) held |= KEY_A;
        if (SDL_JoystickGetButton(s_joy2, 1)) held |= KEY_B;
    }
    return held;
}

static void sample_p2(uint64_t frame) {
    if (frame == s_polled_frame) return;
    s_polled_frame = frame;
    uint8_t held = poll_p2();
    s_pressed = (uint8_t)(held & ~s_prev_held);
    s_prev_held = held;
    s_held = held;
}

static void give_p2_keys(GBContext *ctx) {
    ctx->hram[0] = s_held;
    ctx->hram[1] = s_pressed;
}

static void run_real(GBContext *ctx, uint16_t addr) {
    if (s_real_dispatch) s_real_dispatch(ctx, addr);
}

static void coop_log(const char *fmt, ...) {
    if (!s_log) {
        char path[512];
        gb_host_state_path("sml2-coop.log", path, sizeof path);
        s_log = fopen(path, "a");
        if (!s_log) return;
        fprintf(s_log, "--- coop log %s ---\n", path);
        fflush(s_log);
    }
    va_list ap;
    va_start(ap, fmt);
    vfprintf(s_log, fmt, ap);
    va_end(ap);
    fputc('\n', s_log);
    fflush(s_log);
}

/* The body's dispatch runs until HALT, and after the frame is done every
 * ticked instruction raises ctx->stopped. Either one aborts the routine
 * on its first instruction. Step one instruction at a time, ignore that
 * stop flag, and finish when the routine returns to the sentinel. */
static void pump_call(GBContext *ctx, uint16_t func) {
    uint16_t saved_sp = ctx->sp;
    uint16_t saved_pc = ctx->pc;
    uint16_t saved_rom = ctx->rom_bank;
    uint8_t saved_ram = ctx->ram_bank;
    uint8_t saved_wram = ctx->wram_bank;
    uint8_t saved_halted = ctx->halted;
    uint8_t saved_stopped = ctx->stopped;
    uint8_t saved_done = ctx->frame_done;
    uint8_t saved_step = ctx->single_step_mode;
    ctx->halted = 0;
    ctx->stopped = 0;
    ctx->frame_done = 0;
    ctx->single_step_mode = 1;
    gb_push16(ctx, 0x0001);
    ctx->pc = func;
    s_pumping = 1;
    int steps = 0;
    uint8_t done_during = 0;
    for (; steps < 20000; steps++) {
        if (ctx->pc == 0x0001) break;
        ctx->stopped = 0;
        ctx->frame_done = 0;
        ctx->halted = 0;
        uint16_t before = ctx->pc;
        run_real(ctx, before);
        if (ctx->frame_done) done_during = 1;
        if (ctx->pc == before) break;
    }
    s_pumping = 0;
    s_pump_steps = steps;
    s_pump_pc = ctx->pc;
    ctx->single_step_mode = saved_step;
    ctx->halted = saved_halted;
    ctx->stopped = saved_stopped;
    ctx->frame_done = (uint8_t)(saved_done | done_during);
    ctx->sp = saved_sp;
    ctx->pc = saved_pc;
    ctx->rom_bank = saved_rom;
    ctx->ram_bank = saved_ram;
    ctx->wram_bank = saved_wram;
}

/* Drop a called routine without running it. The CALL already pushed
 * the return address. */
static void skip_call(GBContext *ctx) {
    uint16_t ret = gb_pop16(ctx);
    ctx->pc = ret;
    run_real(ctx, ret);
}

static void begin_other(GBContext *ctx, int phase, uint16_t func, uint16_t ret_pc) {
    save_regs(ctx);
    remember_keys(ctx);
    s_mode_before = mode_of(ctx);
    save_player(ctx, &s_pl[s_lead]);
    /* Player 2's buttons, unless he is already the body in the registers
     * and the ghost is player 1 — those keys are what the ROM just stored. */
    s_lock_p2 = ghost_index() == 1;
    if (s_lock_p2) give_p2_keys(ctx);
    load_player(ctx, &s_pl[ghost_index()]);
    if (phase == PHASE_HIT) write_screen(ctx);
    s_phase = phase;
    gb_push16(ctx, ret_pc);
    ctx->pc = func;
    run_real(ctx, func);
}

static void restore_lead(GBContext *ctx) {
    load_player(ctx, &s_pl[s_lead]);
    load_regs(ctx);
    restore_keys(ctx);
    s_lock_p2 = 0;
    s_phase = PHASE_IDLE;
}

/* The player who is not in the registers just finished 00:0F71. */
static void finish_move(GBContext *ctx) {
    int pipe = piping(ctx);
    int mode = mode_of(ctx);
    uint8_t hurt = eram_at(ctx, 0xA224);
    int y = hram16(ctx, SML2_MARIO_Y);
    int g = ghost_index();
    save_player(ctx, &s_pl[g]);

    if (pipe) {
        s_pl[s_lead].hide = 1;
        s_lead = g;
        s_in_pipe = 1;
        load_regs(ctx);
        restore_keys(ctx);
        s_lock_p2 = 0;
        s_phase = PHASE_IDLE;
        run_real(ctx, PC_AFTER_MOVE);
        return;
    }

    int dead = mode == MODE_DEAD || hurt == 0xFF || hurt == 0x80 || y > 780;
    if (dead) {
        s_pl[g].alive = 0;
        s_pl[g].hide = 0;
        s_pl[g].respawn = RESPAWN_FRAMES;
        restore_lead(ctx);
        mode_set(ctx, s_mode_before);
    } else {
        restore_lead(ctx);
    }
    run_real(ctx, PC_AFTER_MOVE);
}

static void finish_hit(GBContext *ctx) {
    int g = ghost_index();
    int stomped = eram_at(ctx, 0xA2D4) != 0;
    uint8_t hurt = eram_at(ctx, 0xA224);
    save_player(ctx, &s_pl[g]);
    if (stomped) {
        s_pl[g].vy = (s_held & KEY_A) ? -5 * PX : -3 * PX;
        s_pl[g].grounded = 0;
        blob_set(&s_pl[g], 0xA201, 0x10);
        blob_set(&s_pl[g], 0xA214, 0);
    } else if (hurt == 0x0F || hurt == 0xFF || hurt == 0x80) {
        uint8_t power = blob_get(&s_pl[g], 0xA216);
        if (power == 0 || hurt == 0xFF || hurt == 0x80) {
            s_pl[g].alive = 0;
            s_pl[g].hide = 0;
            s_pl[g].respawn = RESPAWN_FRAMES;
            s_pl[g].vx = s_pl[g].vy = 0;
            s_pl[g].grounded = 0;
        } else {
            blob_set(&s_pl[g], 0xA216, (uint8_t)(power == 2 ? 1 : 0));
            blob_set(&s_pl[g], 0xA224, 0);
            blob_set(&s_pl[g], 0xA217, 0x40);
        }
    }
    restore_lead(ctx);
    run_real(ctx, PC_AFTER_HIT);
}

/* A pipe ride just released the registers. Put player 1 back in them
 * when he is waiting, and stand the other one next to the exit. */
static void arrive(GBContext *ctx) {
    if (s_lead == 1 && s_pl[0].alive) {
        save_player(ctx, &s_pl[1]);
        set_pos(&s_pl[0], s_pl[1].x, s_pl[1].y);
        set_idle(&s_pl[0]);
        s_pl[0].alive = 1;
        s_pl[0].hide = 0;
        load_player(ctx, &s_pl[0]);
        s_lead = 0;
        set_pos(&s_pl[1], s_pl[0].x + 18, s_pl[0].y);
        set_idle(&s_pl[1]);
        s_pl[1].alive = 1;
        s_pl[1].hide = 0;
        return;
    }
    Player *g = &s_pl[ghost_index()];
    g->hide = 0;
    if (!g->alive) return;
    set_pos(g, hram16(ctx, SML2_MARIO_X) + 18, hram16(ctx, SML2_MARIO_Y));
    set_idle(g);
}

static void maybe_start_move(GBContext *ctx) {
    if (s_in_pipe && !piping(ctx)) arrive(ctx);
    if (piping(ctx)) {
        s_in_pipe = 1;
        run_real(ctx, PC_AFTER_MOVE);
        return;
    }
    s_in_pipe = 0;
    run_real(ctx, PC_AFTER_MOVE);
}

/* Blocks, coins and enemies live in the ROM. Run those routines on his
 * position, then put his own walk back so they cannot drag him. */
static void interact_p2(GBContext *ctx) {
    Player *p = &s_pl[1];
    s_hit_frames++;
    if (s_lead != 0 || !p->alive || p->hide || (p->x | p->y) == 0) {
        if (s_hit_frames <= 8 || (s_hit_frames % 120) == 0)
            coop_log("hit %d skip lead=%d alive=%d hide=%d x=%d y=%d",
                     s_hit_frames, s_lead, p->alive, p->hide, p->x, p->y);
        return;
    }
    int keep_x = p->x, keep_y = p->y;
    int keep_fx = p->fx, keep_fy = p->fy;
    int keep_vx = p->vx, keep_vy = p->vy;
    int keep_ground = p->grounded;
    uint8_t coins_before = eram_at(ctx, 0xA262);
    uint8_t snd460 = eram_at(ctx, 0xA460);
    uint8_t snd468 = eram_at(ctx, 0xA468);
    uint8_t snd470 = eram_at(ctx, 0xA470);
    uint8_t snd478 = eram_at(ctx, 0xA478);
    int mode_before = mode_of(ctx);

    save_regs(ctx);
    remember_keys(ctx);
    save_player(ctx, &s_pl[s_lead]);
    s_lock_p2 = 1;
    give_p2_keys(ctx);
    load_player(ctx, p);
    write_screen(ctx);
    bias_x(ctx, -8);
    pump_call(ctx, PC_BLOCKS);
    int blocks_steps = s_pump_steps;
    uint16_t blocks_pc = s_pump_pc;
    pump_call(ctx, PC_BODY);
    int body_steps = s_pump_steps;
    uint16_t body_pc = s_pump_pc;
    memcpy(ctx->hram + (0xFFC0 - 0xFF80), p->pos, 4);
    pump_call(ctx, PC_HIT);
    int hit_steps = s_pump_steps;
    uint16_t hit_pc = s_pump_pc;

    int stomped = eram_at(ctx, 0xA2D4) != 0;
    uint8_t hurt = eram_at(ctx, 0xA224);
    uint8_t coins = eram_at(ctx, 0xA262);
    int feet = level_byte(ctx, 0xB000u
        + ((unsigned)((keep_y + SQUARE_TOP + SQUARE_H) >> 4) & 0xFFu) * 0x100u
        + ((unsigned)(keep_x >> 4) & 0xFFu));
    int above = level_byte(ctx, 0xB000u
        + ((unsigned)((keep_y + SQUARE_TOP - 1) >> 4) & 0xFFu) * 0x100u
        + ((unsigned)(keep_x >> 4) & 0xFFu));
    save_player(ctx, p);
    set_pos(p, keep_x, keep_y);
    p->fx = keep_fx;
    p->fy = keep_fy;
    p->vx = keep_vx;
    p->vy = keep_vy;
    p->grounded = keep_ground;
    int killed = 0;
    if (stomped) {
        p->vy = (s_held & KEY_A) ? -5 * PX : -3 * PX;
        p->grounded = 0;
        blob_set(p, 0xA201, 0x10);
        blob_set(p, 0xA214, 0);
    } else if (hurt == 0x0F || hurt == 0xFF || hurt == 0x80) {
        uint8_t power = blob_get(p, 0xA216);
        if (power == 0 || hurt == 0xFF || hurt == 0x80) {
            p->alive = 0;
            p->hide = 0;
            p->respawn = RESPAWN_FRAMES;
            p->vx = p->vy = 0;
            p->grounded = 0;
            killed = 1;
        } else {
            blob_set(p, 0xA216, (uint8_t)(power == 2 ? 1 : 0));
            blob_set(p, 0xA224, 0);
            blob_set(p, 0xA217, 0x40);
        }
    }
    if (killed) {
        /* 00:2D7D queues the death jingle in $A460. That replaces the
         * level song. His death is local, so the song stays. */
        eram_put(ctx, 0xA460, snd460);
        eram_put(ctx, 0xA468, snd468);
        eram_put(ctx, 0xA470, snd470);
        eram_put(ctx, 0xA478, snd478);
        if (mode_of(ctx) == MODE_DEAD) mode_set(ctx, mode_before);
    }
    int interesting = stomped || hurt || coins != coins_before
        || blocks_pc != 0x0001 || body_pc != 0x0001 || hit_pc != 0x0001
        || blocks_steps >= 20000 || body_steps >= 20000 || hit_steps >= 20000;
    if (s_hit_frames <= 40 || interesting || (s_hit_frames % 60) == 0)
        coop_log("hit %d x=%d y=%d feet=%02X above=%02X coins %02X->%02X "
                 "blocks %d/%04X body %d/%04X enemies %d/%04X stomp=%d hurt=%02X",
                 s_hit_frames, keep_x, keep_y, feet & 0xFF, above & 0xFF,
                 coins_before, coins,
                 blocks_steps, blocks_pc, body_steps, body_pc,
                 hit_steps, hit_pc, stomped, hurt);
    load_player(ctx, &s_pl[s_lead]);
    load_regs(ctx);
    restore_keys(ctx);
    s_lock_p2 = 0;
}

static void maybe_start_hit(GBContext *ctx) {
    run_real(ctx, PC_AFTER_HIT);
}

/* The frame loop calls this for every instruction, from inside the
 * dispatch that actually runs the ROM. The co-op wrapper only sees the
 * first address of each wake, so the block and enemy routines have to
 * start here. Return 0 so the real instruction still runs. */
int game_dispatch_override(struct GBContext *ctx, uint16_t addr) {
    if (!s_on || s_pumping || !ctx || addr != PC_AFTER_HIT) return 0;
    if (mode_of(ctx) != MODE_PLAY || s_in_pipe) return 0;
    interact_p2(ctx);
    return 0;
}

/* 00:0640 is the death bounce. It is a direct call, so the first
 * dispatch we see is its return. If the other player is up, step into
 * his body before the life counter runs. */
static void maybe_takeover(GBContext *ctx) {
    int live = ghost_index();
    if (!s_pl[live].alive || s_pl[live].hide || s_in_pipe) return;
    s_pl[s_lead].alive = 0;
    s_pl[s_lead].hide = 0;
    s_pl[s_lead].respawn = RESPAWN_FRAMES;
    s_lead = live;
    load_player(ctx, &s_pl[live]);
    mode_set(ctx, MODE_PLAY);
}

static void coop_dispatch(GBContext *ctx, uint16_t addr) {
    if (!s_on || !ctx || !ctx->hram || s_blob_n <= 0) {
        run_real(ctx, addr);
        return;
    }
    if (s_phase == PHASE_MOVE &&
        (addr == PC_CLAMP || addr == PC_SHOT_A || addr == PC_SHOT_B)) {
        skip_call(ctx);
        return;
    }
    if (addr == PC_AFTER_MOVE && s_phase == PHASE_MOVE) {
        finish_move(ctx);
        return;
    }
    if (addr == PC_AFTER_HIT && s_phase == PHASE_HIT) {
        finish_hit(ctx);
        return;
    }
    if (s_phase != PHASE_IDLE) {
        run_real(ctx, addr);
        return;
    }
    if (addr == PC_AFTER_DEAD) {
        maybe_takeover(ctx);
        run_real(ctx, addr);
        return;
    }
    if (addr == PC_AFTER_MOVE) {
        maybe_start_move(ctx);
        return;
    }
    if (addr == PC_AFTER_HIT) {
        maybe_start_hit(ctx);
        return;
    }
    run_real(ctx, addr);
}

static void coop_dispatch_call(GBContext *ctx, uint16_t addr) {
    if (s_real_dispatch_call) s_real_dispatch_call(ctx, addr);
    else gb_dispatch_call(ctx, addr);
}

/* Bring the waiting player back beside the one in the registers.
 * Player 1 always returns to the registers, so player 2 stays the
 * recolored body once both are alive. */
static void respawn_other(GBContext *ctx) {
    if ((hram16(ctx, SML2_MARIO_X) | hram16(ctx, SML2_MARIO_Y)) == 0) return;
    if (s_lead == 1) {
        save_player(ctx, &s_pl[1]);
        s_pl[0] = s_pl[1];
        set_pos(&s_pl[0], s_pl[1].x, s_pl[1].y);
        set_idle(&s_pl[0]);
        s_pl[0].alive = 1;
        s_pl[0].hide = 0;
        s_pl[0].respawn = 0;
        load_player(ctx, &s_pl[0]);
        s_lead = 0;
        set_pos(&s_pl[1], s_pl[0].x + 18, s_pl[0].y);
        set_idle(&s_pl[1]);
        s_pl[1].alive = 1;
        s_pl[1].hide = 0;
        s_pl[1].respawn = 0;
        return;
    }
    save_player(ctx, &s_pl[1]);
    set_pos(&s_pl[1], s_pl[1].x + 18, s_pl[1].y);
    set_idle(&s_pl[1]);
    s_pl[1].alive = 1;
    s_pl[1].hide = 0;
    s_pl[1].respawn = 0;
}

/* Stand player 2 on Mario's floor sample, a short step to his right. */
static void beside_mario(GBContext *ctx) {
    int x = hram16(ctx, SML2_MARIO_X);
    int y = hram16(ctx, SML2_MARIO_Y);
    if ((x | y) == 0 || s_lead != 0) return;
    set_pos(&s_pl[1], x + 18, y);
    set_idle(&s_pl[1]);
    s_pl[1].alive = 1;
    s_pl[1].hide = 0;
    s_pl[1].respawn = 0;
}

static void coop_snapshot(GBContext *ctx) {
    if (s_prev_snapshot) s_prev_snapshot(ctx);
    if (s_pumping) return;
    if (!s_on || !ctx || !ctx->hram || s_phase != PHASE_IDLE) return;
    sample_p2(ctx->completed_frames);

    int level = eram_at(ctx, 0xA269) | (eram_at(ctx, 0xA258) << 8);
    int mode = mode_of(ctx);
    int mx = hram16(ctx, SML2_MARIO_X);
    int my = hram16(ctx, SML2_MARIO_Y);
    int entered = level != s_level || (mode == MODE_PLAY && s_prev_mode != MODE_PLAY);
    if (!entered && mode == MODE_PLAY && !s_in_pipe && s_track_x >= 0) {
        int dx = mx - s_track_x;
        int dy = my - s_track_y;
        if (dx < 0) dx = -dx;
        if (dy < 0) dy = -dy;
        /* A level load, a door or a pipe exit. A jump never moves this far. */
        if (dx > 64 || dy > 48) entered = 1;
    }
    s_level = level;
    s_prev_mode = mode;
    if (mode == MODE_PLAY && (mx | my)) {
        s_track_x = mx;
        s_track_y = my;
    }
    if (entered) {
        s_lead = 0;
        s_in_pipe = 0;
        beside_mario(ctx);
    }
    if (mode != MODE_PLAY || s_in_pipe) return;
    Player *g = &s_pl[ghost_index()];
    if (!entered) {
        if (g->respawn > 0) g->respawn--;
        if (!g->alive && g->respawn == 0) respawn_other(ctx);
    }
    step_p2(ctx);
    if ((ctx->completed_frames % 60ull) == 0)
        coop_log("snap frame=%llu mode=%d lead=%d p2=%d,%d alive=%d hits=%d",
                 (unsigned long long)ctx->completed_frames, mode, s_lead,
                 s_pl[1].x, s_pl[1].y, s_pl[1].alive, s_hit_frames);
}

static uint8_t coop_read(GBContext *ctx, uint16_t addr, uint8_t value) {
    if (s_prev_override) value = s_prev_override(ctx, addr, value);
    /* Whoever is in the registers sees only his own buttons. Mario's
     * latched pad must not also walk the green player, or the reverse. */
    if (s_lock_p2 || (s_lead == 1 && s_phase == PHASE_IDLE)) {
        if (addr == 0xFF80) value = s_held;
        else if (addr == 0xFF81) value = s_pressed;
    }
    return value;
}

static void plot(uint32_t *out, int width, int x, int y, uint32_t color) {
    if ((unsigned)x >= (unsigned)width || (unsigned)y >= GB_SCREEN_HEIGHT) return;
    if (y >= HUD_Y) return;
    out[(size_t)y * width + x] = color;
}

static uint32_t green_shade(const GBContext *ctx, int pal, int color, uint8_t attr) {
    int y;
    if (ctx->config.model == GB_MODEL_CGB && ctx->ppu) {
        const GBPPU *ppu = (const GBPPU *)ctx->ppu;
        unsigned i = (unsigned)(pal * 8 + color * 2);
        uint16_t c = (uint16_t)(ppu->obj_palette_ram[i] |
                                (ppu->obj_palette_ram[i + 1] << 8));
        int r = (c & 31) * 255 / 31;
        int g = ((c >> 5) & 31) * 255 / 31;
        int b = ((c >> 10) & 31) * 255 / 31;
        y = (r * 30 + g * 59 + b * 11) / 100;
    } else {
        uint8_t obp = 0xE4;
        if (ctx->ppu) {
            const GBPPU *ppu = (const GBPPU *)ctx->ppu;
            obp = (attr & 0x10) ? ppu->obp1 : ppu->obp0;
        }
        static const int lum[4] = { 255, 170, 85, 0 };
        y = lum[(obp >> (color * 2)) & 3];
    }
    if (y < 0) y = 0;
    if (y > 255) y = 255;
    return 0xFF000000u | ((unsigned)(y / 4) << 16) | ((unsigned)y << 8) | (unsigned)(y / 5);
}

static const uint8_t *metasprite(const GBContext *ctx, int index) {
    if (!ctx->rom || index < 0 || index > 255) return NULL;
    /* The faithful cart keeps the table in bank 1. DX moves it to bank
     * $2C or $2D (picked from $FFF6) and, on some levels, to $6000. */
    int bank = 1;
    unsigned table = 0x4000u;
    if (ctx->rom_size > 0x80000u) {
        uint8_t page = ctx->hram ? ctx->hram[0xFFF6u - 0xFF80u] : 0;
        bank = (page & 0x0F) == 1 ? 0x2D : 0x2C;
        if (eram_at(ctx, 0xA21A) & 0xF0) table = 0x6000u;
    }
    size_t off = (size_t)bank * 0x4000u + (table - 0x4000u) + (unsigned)index * 2u;
    if (off + 1 >= ctx->rom_size) return NULL;
    unsigned ptr = ctx->rom[off] | ((unsigned)ctx->rom[off + 1] << 8);
    if (ptr < 0x4000u || ptr >= 0x8000u) return NULL;
    size_t poff = (size_t)bank * 0x4000u + (ptr - 0x4000u);
    if (poff >= ctx->rom_size) return NULL;
    return ctx->rom + poff;
}

/* Same sheet Mario uses. The frame comes from his own speed and facing,
 * so player 1's pose does not drive it. */
static int mario_frame(const Player *p) {
    int right = p->face != 0;
    int base;
    if (!p->grounded)
        base = p->vy < 0 ? (right ? 8 : 9) : (right ? 10 : 11);
    else if (p->vx > -40 && p->vx < 40)
        base = right ? 0 : 4;
    else if ((right && p->vx < 0) || (!right && p->vx > 0))
        base = right ? 13 : 12;
    else {
        /* $A222 counts 0..11, so (timer & $0C) >> 2 is only 0, 1 or 2.
         * The fourth step is the other direction's idle, and past that
         * the jump pose with the arm up. */
        int step = (p->anim >> 2) % 3;
        base = right ? 1 + step : 5 + step;
    }
    int power = blob_get(p, 0xA216);
    int mercy = blob_get(p, 0xA217);
    if (mercy & 4) base += 32;
    else if (power == 0) base += 32;
    else if (power == 2) base += 69;
    else if (power == 3) base += 112;
    return base;
}

static void blit_tile(uint32_t *out, int width, const GBContext *ctx,
                      int dx, int dy, uint8_t tile, uint8_t attr) {
    if (!ctx->vram) return;
    unsigned bank = ((attr & 0x08) && ctx->config.model == GB_MODEL_CGB) ? 1u : 0u;
    const uint8_t *src = ctx->vram + bank * 0x2000u + (unsigned)tile * 16u;
    int flip_x = (attr & 0x20) != 0;
    int flip_y = (attr & 0x40) != 0;
    int pal = attr & 7;
    for (int row = 0; row < 8; row++) {
        int sy = flip_y ? 7 - row : row;
        uint8_t lo = src[sy * 2];
        uint8_t hi = src[sy * 2 + 1];
        for (int col = 0; col < 8; col++) {
            int bit = flip_x ? col : 7 - col;
            int color = ((lo >> bit) & 1) | (((hi >> bit) & 1) << 1);
            if (!color) continue;
            plot(out, width, dx + col, dy + row, green_shade(ctx, pal, color, attr));
        }
    }
}

static void draw_other(GBContext *ctx, uint32_t *out, int width) {
    const Player *g = &s_pl[1];
    /* While he occupies Mario's registers the ROM is already drawing him. */
    if (s_lead == 1 || !g->alive || !ctx->hram) return;
    int cam_x = hram16(ctx, SML2_CAM_X);
    int cam_y = hram16(ctx, SML2_CAM_Y);
    int origin = (width - GB_SCREEN_WIDTH) / 2;
    int centre = origin + (g->x - cam_x + SML2_CAM_CENTRE_X);
    int feet = (g->y + SQUARE_TOP + SQUARE_H + DRAW_DROP - cam_y + SML2_CAM_CENTRE_Y);
    const uint8_t *ms = metasprite(ctx, mario_frame(g));
    if (!ms) {
        int left = centre - 8;
        int top = feet - SQUARE_H;
        for (int row = 0; row < 16; row++)
            for (int col = 0; col < 16; col++)
                plot(out, width, left + col, top + row, 0xFF20E020u);
        return;
    }
    int minx = 127, miny = 127, maxx = -128, maxy = -128, n = 0;
    int xoff[16], yoff[16];
    uint8_t tile[16], attr[16];
    for (; n < 16; n++) {
        if (ms[n * 4] == 0x80) break;
        yoff[n] = (int)(int8_t)ms[n * 4];
        xoff[n] = (int)(int8_t)ms[n * 4 + 1];
        tile[n] = ms[n * 4 + 2];
        attr[n] = ms[n * 4 + 3];
        if (xoff[n] < minx) minx = xoff[n];
        if (yoff[n] < miny) miny = yoff[n];
        if (xoff[n] + 8 > maxx) maxx = xoff[n] + 8;
        if (yoff[n] + 8 > maxy) maxy = yoff[n] + 8;
    }
    if (n == 0) return;
    int left = centre - (maxx - minx) / 2 - minx;
    int top = feet - (maxy - miny) - miny;
    for (int i = 0; i < n; i++)
        blit_tile(out, width, ctx, left + xoff[i], top + yoff[i], tile[i], attr[i]);
}

static void fill_native(uint32_t *out, int width, const uint32_t *native) {
    int left = (width - GB_SCREEN_WIDTH) / 2;
    if (left < 0) left = 0;
    for (int y = 0; y < GB_SCREEN_HEIGHT; y++) {
        uint32_t *row = out + (size_t)y * width;
        for (int x = 0; x < width; x++) row[x] = 0xFF000000u;
        if (!native || left >= width) continue;
        int n = GB_SCREEN_WIDTH;
        if (left + n > width) n = width - left;
        memcpy(row + left, native + (size_t)y * GB_SCREEN_WIDTH, (size_t)n * sizeof(uint32_t));
    }
}

static int coop_render(GBContext *ctx, uint32_t *out, int width, const uint32_t *native) {
    int ok = 0;
    if (s_prev_render) ok = s_prev_render(ctx, out, width, native);
    if (!ok) fill_native(out, width, native);
    if (ctx && ctx->hram && mode_of(ctx) == MODE_PLAY)
        draw_other(ctx, out, width);
    return 1;
}

static void coop_reset(GBContext *ctx) {
    if (s_prev_reset) s_prev_reset(ctx);
    memset(s_pl, 0, sizeof s_pl);
    s_lead = 0;
    s_phase = PHASE_IDLE;
    s_in_pipe = 0;
    s_level = -1;
    s_prev_mode = -1;
    s_track_x = -1;
    s_track_y = -1;
    s_held = s_pressed = s_prev_held = 0;
    s_lock_p2 = 0;
    s_polled_frame = ~0ull;
}

void sml2_coop_init(GBContext *ctx) {
    (void)ctx;
    s_on = sml2_mod_settings()->coop != 0;
    if (!s_on) return;
    load_p2_input();
    bind_addrs();
    if (s_blob_n <= 0 || s_blob_n > BLOB_MAX) { s_on = 0; return; }
    coop_reset(NULL);
    const GBBody *body = gb_body_active();
    if (body && body->dispatch) {
        s_real_dispatch = body->dispatch;
        s_real_dispatch_call = body->dispatch_call;
    } else {
        s_real_dispatch = gb_dispatch;
        s_real_dispatch_call = gb_dispatch_call;
    }
    gb_set_dispatch(coop_dispatch, coop_dispatch_call);
    s_prev_render = gb_custom_render;
    s_prev_snapshot = gb_custom_snapshot;
    s_prev_reset = gb_custom_reset;
    s_prev_override = gb_custom_read_override;
    gb_custom_render = coop_render;
    gb_custom_snapshot = coop_snapshot;
    gb_custom_reset = coop_reset;
    gb_custom_read_override = coop_read;
    if (!s_prev_render) gb_custom_requested_width = GB_SCREEN_WIDTH;
}

/* While co-op is on and Player 2 is the keyboard, his keys are not also
 * Mario's. J and K are Mario's secondary A and B otherwise. */
int game_claims_scancode(int scancode) {
    if (!s_on || s_p2_src != 1 || scancode <= 0) return 0;
    for (int b = 0; b < P2N; b++) {
        if (s_p2_key[b][0] == scancode || s_p2_key[b][1] == scancode)
            return 1;
    }
    return 0;
}
