/*
 * Adapted from WACC chapter_19/dead_store_elimination/int_only/dont_elim/add_all_to_worklist.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the optimizer behavior and
 * the original program's return value remain under test.
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

/* Make sure we add every basic block to the worklist
 * at the start of the iterative algorithm
 */

int f(int arg) {
    int x = 76;
    if (arg < 10) {
        // give x multiple values on different paths
        // so we can't propagate it
        x = 77;
    }
    // no live variables flow into this basic block from its successor,
    // bu we still need to process it to learn that x is live
    if (arg)
        wacc_emit_char(x);
    return 0;
}

int wacc_program_main(void) {
    f(0);
    f(1);
    f(11);
    return 0;
}

int main(void) {
    const char *expected_output = "ML";
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
