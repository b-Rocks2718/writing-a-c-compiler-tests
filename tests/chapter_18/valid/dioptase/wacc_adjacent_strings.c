/*
 * Adapted from WACC chapter_16/valid/strings_as_lvalues/adjacent_strings.c.
 * Compare bytes in memory because the emulator CRT has no puts.
 */
#define TEST_OK 0
#define BAD_CONCATENATION 1

int main(void) {
    const char *actual = "Hello," " World";
    const char *expected = "Hello, World";
    for (int i = 0; expected[i] != 0; i = i + 1) {
        if (actual[i] != expected[i])
            return BAD_CONCATENATION;
    }
    if (actual[sizeof("Hello, World") - 1] != 0)
        return BAD_CONCATENATION;
    return TEST_OK;
}
