// semmle-extractor-options: -std=c++17

static int plain; // $ Alert[cpp/unused-static-variable]
static int aligned __attribute__((aligned(16))); // $ Alert[cpp/unused-static-variable]
static int used __attribute__((used));
static int unused __attribute__((unused));
[[maybe_unused]] static int maybeUnused;
static int usedAndAligned __attribute__((used, aligned(16)));
static int unusedAndAligned __attribute__((unused, aligned(16)));
[[maybe_unused]] static int maybeUnusedAndAligned __attribute__((aligned(16)));
[[maybe_unused]] static int all __attribute__((used, unused));
