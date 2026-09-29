/*
 * Adapted from WACC chapter_19/dead_store_elimination/int_only/dont_elim/dont_remove_funcall.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the optimizer behavior and
 * the original program's return value remain under test.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 1
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

/* Test that we never optimize away function calls,
 * even if they're dead stores (i.e. update dead variables)
 * because they can have side effects */
#if defined SUPPRESS_WARNINGS
#pragma GCC diagnostic ignored "-Wunused-variable"
#endif


int wacc_program_main(void) {
    // Make sure we don't optimize away this function call.
    // It would be safe to keep the function call, but optimize out
    // the store to x (i.e. get rid of movl %eax, %x), but our implementation
    // doesn't.
    int x = wacc_emit_char(67);
    return 0;
}

int main(void) {
    const char *expected_output = "C";
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
