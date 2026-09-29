/*
 * Adapted from WACC chapter_17/valid/void/void_for_loop.c.
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

/* Test for void expressions in for loop header */


int letter;
void initialize_letter(void) {
    letter = 'Z';
}

void decrement_letter(void) {
    letter = letter - 1;
}

int wacc_program_main(void) {
    // void expression in initial condition: print the alphabet backwards
    for (initialize_letter(); letter >= 'A';
         letter = letter - 1) {
        wacc_emit_char(letter);
    }

    // void expression in post condition: print the alphabet forwards
    for (letter = 'A'; letter <= 90; (void)(letter = letter + 1)) {
        wacc_emit_char(letter);
    }

    // void expressions in both conditions: print the alphabet backwards again
    for (initialize_letter(); letter >= 65; decrement_letter()) {
        wacc_emit_char(letter);
    }
    return 0;
}

int main(void) {
    const char *expected_output = "ZYXWVUTSRQPONMLKJIHGFEDCBAABCDEFGHIJKLMNOPQRSTUVWXYZZYXWVUTSRQPONMLKJIHGFEDCBA";
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
