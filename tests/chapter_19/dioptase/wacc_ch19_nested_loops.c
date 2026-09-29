/*
 * Adapted from WACC chapter_19/dead_store_elimination/int_only/dont_elim/nested_loops.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the optimizer behavior and
 * the original program's return value remain under test.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 5
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

/* Test that the algorithm runs until it converges;
 * some blocks need to be visited three times before the algorithm converges
 * */


int target(int a, int b, int c, int d) {
    while (a > 0) {
        while (c > 0) {
            wacc_emit_char(c + d);
            c = c - 1;
            if (d % 2) {
                c = c - 2;
            }
        }

        while (b > 0) {
            c = 10;  // this is not dead, b/c it's used in previous while
                     // loop, but it takes multiple passes for that
                     // information to propagate to this point
            b = b - 1;
        }

        a = a - 1;
    }
    return 0;
}

int wacc_program_main(void) {
    return target(5, 4, 3, 65);
}

int main(void) {
    const char *expected_output = "DKHEB";
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
