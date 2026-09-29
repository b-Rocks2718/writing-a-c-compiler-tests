/* Test string escapes and literal contents from WACC chapter 16 without
 * depending on the target C library's puts or strcmp implementations. */

static int same_string(const char *actual, const char *expected) {
    int i = 0;
    while (actual[i] && expected[i]) {
        if (actual[i] != expected[i]) {
            return 0;
        }
        i++;
    }
    return actual[i] == expected[i];
}

int main(void) {
    char *escape_sequence = "\a\b";
    if (escape_sequence[0] != 7) return 1;
    if (escape_sequence[1] != 8) return 2;
    if (escape_sequence[2]) return 3;

    char *with_double_quote = "Hello\"world";
    if (with_double_quote[5] != '"') return 4;
    if (!same_string(with_double_quote, "Hello\"world")) return 8;

    char *with_backslash = "Hello\\World";
    if (with_backslash[5] != '\\') return 5;
    if (!same_string(with_backslash, "Hello\\World")) return 9;

    char *with_newline = "Line\nbreak!";
    if (with_newline[4] != 10) return 6;
    if (!same_string(with_newline, "Line\nbreak!")) return 10;

    char *tab = "\t";
    if (!same_string(tab, "\t")) return 7;
    char expected_digits[14] = {'T', 'e', 's', 't', 'i', 'n', 'g', ',',
                              ' ', '1', '2', '3', '.', 0};
    char expected_punctuation[8] = {'^', '@', '1', ' ', '_', '\\', ']', 0};
    if (!same_string("Testing, 123.", expected_digits)) return 11;
    if (!same_string("^@1 _\\]", expected_punctuation)) return 12;
    return 0;
}
