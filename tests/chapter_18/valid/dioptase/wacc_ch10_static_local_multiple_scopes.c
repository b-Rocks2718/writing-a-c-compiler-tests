/*
 * Adapted from WACC chapter_10/valid/static_local_multiple_scopes.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the original program's
 * return value and control flow remain under test.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 78
#define WACC_TEST_OK 0
#define WACC_BAD_RETURN 1
#define WACC_BAD_OUTPUT 2

static char wacc_captured_output[WACC_EXPECTED_LENGTH];
static int wacc_captured_length;
static int wacc_output_overflow;

int wacc_emit_char(int c) {
    if (wacc_captured_length == WACC_EXPECTED_LENGTH) {
        wacc_output_overflow = 1;
    } else {
        wacc_captured_output[wacc_captured_length] = (char)c;
        wacc_captured_length = wacc_captured_length + 1;
    }
    return c;
}

/* static local variables declared in different scopes
 * in the same function are distinct from each other.
 */


int print_letters(void) {
    /* declare a static variable, initialize to ASCII 'A' */
    static int i = 65;
    /* print the ASCII character for its current value */
    wacc_emit_char(i);
    {
        /* update the outer static 'i' variable */
        i = i + 1;

        /* declare another static variable, initialize to ASCII 'a' */
        static int i = 97;
        /* print the ASCII character for inner variable's current value */
        wacc_emit_char(i);
        /* increment inner variable's value */
        i = i + 1;
    }
    /* print a newline */
    wacc_emit_char(10);
    return 0;
}

int wacc_program_main(void) {
    //print uppercase and lowercase version of each letter in the alphabet
    for (int i = 0; i < 26; i = i + 1)
        print_letters();
}

int main(void) {
    const char *expected_output = "Aa\nBb\nCc\nDd\nEe\nFf\nGg\nHh\nIi\nJj\nKk\nLl\nMm\nNn\nOo\nPp\nQq\nRr\nSs\nTt\nUu\nVv\nWw\nXx\nYy\nZz\n";
    int original_result = wacc_program_main();
    if (original_result != WACC_EXPECTED_RETURN)
        return WACC_BAD_RETURN;
    if (wacc_output_overflow || wacc_captured_length != WACC_EXPECTED_LENGTH)
        return WACC_BAD_OUTPUT;
    for (int i = 0; i < WACC_EXPECTED_LENGTH; i = i + 1) {
        if (wacc_captured_output[i] != expected_output[i])
            return WACC_BAD_OUTPUT;
    }
    return WACC_TEST_OK;
}
