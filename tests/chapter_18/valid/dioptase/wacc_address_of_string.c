/*
 * Adapted from WACC chapter_16/valid/strings_as_lvalues/addr_of_string.c.
 * Check literal contents in memory because the emulator CRT has no puts.
 */
#define TEST_OK 0
#define BAD_TERMINATOR 1
#define BAD_CONTENTS 2

int main(void) {
    char (*str)[16] = &"Sample\tstring!\n";
    const char *expected = "Sample\tstring!\n";
    for (int i = 0; i < 15; i = i + 1) {
        if ((*str)[i] != expected[i])
            return BAD_CONTENTS;
    }
    char (*one_past_the_end)[16] = str + 1;
    char *last_byte_pointer = (char *)one_past_the_end - 1;
    if (*last_byte_pointer != 0)
        return BAD_TERMINATOR;
    return TEST_OK;
}
