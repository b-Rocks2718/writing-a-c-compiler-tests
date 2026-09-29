/*
 * Adapted from WACC chapter_19/whole_pipeline/all_types/alias_analysis_change.c.
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

/* Test that we rerun alias analysis with each pipeline iteration */


int foo(int *ptr) {
    wacc_emit_char(*ptr);
    return 0;
}

int target(void) {
    int x = 10;  // this is a dead store
    int y = 65;
    int *ptr = &y;
    if (0) {
        // on our first pass through the pipeline it will look like x is
        // aliased; on later passes, after unreachable code elimination removes
        // this branch, we'll recognize that x is not aliased
        ptr = &x;
    }
    x = 5;     // this is a dead store, but we'll only recognize this after
               // rerunning alias analysis
    foo(ptr);  // we'll think this makes x live until we recognize that x is not
               // aliased

    return 0;
}

int wacc_program_main(void) {
    return target();
}

int main(void) {
    const char *expected_output = "A";
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
