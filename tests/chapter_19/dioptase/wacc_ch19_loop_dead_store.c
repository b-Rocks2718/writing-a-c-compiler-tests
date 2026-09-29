/*
 * Adapted from WACC chapter_19/dead_store_elimination/int_only/loop_dead_store.c.
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

/* Test that we can detect dead stores in a function with a loop */

int target(void) {
    int x = 5;   // dead store
    int y = 65;  // not a dead store
    do {
        x = y + 2;  // kill x, gen y
        if (y > 70) {
            // make sure we assign to x on multiple paths
            // so copy prop doesn't replace it entirely
            x = y + 3;
        }
        y = wacc_emit_char(x) + 3;  // gen x and y
    } while (y < 90);
    if (x != 90) {
        return 1;  // fail
    }
    if (y != 93) {
        return 2;  // fail
    }
    return 0;  // success
}

int wacc_program_main(void) {
    return target();
}

int main(void) {
    const char *expected_output = "CHNTZ";
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
