#pragma once
struct GBContext;

/* Installs nothing unless Mods → Gameplay → Simultaneous co-op is on.
 * Call after sml2_adaptive_init() so this can wrap its compositor hooks. */
void sml2_coop_init(struct GBContext *ctx);
