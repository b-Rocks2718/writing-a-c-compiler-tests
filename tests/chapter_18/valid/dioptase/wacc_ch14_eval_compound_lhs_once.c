/*
 * Adapted from WACC chapter_14/valid/extra_credit/eval_compound_lhs_once.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the original program's
 * return value and control flow remain under test. The unsupported 5l
 * literal is replaced with 5; the one-evaluation check remains.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 2
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

// Make sure we evaluate the lhs of a compound expression only once

int i = 0;

int *print_A(void) {
    wacc_emit_char(65); // record A
    return &i;
}

int *print_B(void) {
    wacc_emit_char(66); // record B
    return &i;
}

int wacc_program_main(void) {

    // we should record "A" only ONCE
    *print_A() += 5;
    if (i != 5) {
        return 1;
    }

    // record "B" only ONCE. testing with casting operations
    *print_B() += 5;
    if (i != 10) {
        return 2;
    }

    return 0; // success
}


int main(void) {
    const char *expected_output = "AB";
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
