// semmle-extractor-options: -std=c++17

void test_unused_local_attributes()
{
    int plain; // $ Alert[cpp/unused-local-variable]
    int aligned __attribute__((aligned(16))); // $ Alert[cpp/unused-local-variable]
    int unused __attribute__((unused));
    [[maybe_unused]] int maybeUnused;
    int unusedAndAligned __attribute__((unused, aligned(16)));
    [[maybe_unused]] int maybeUnusedAndAligned __attribute__((aligned(16)));
    [[maybe_unused]] int both __attribute__((unused));

    int accessed = 0;
    (void)accessed;
}
