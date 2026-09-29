/*
 * Adapted from WACC chapter_19/copy_propagation/int_only/dont_propagate/source_killed_on_one_path.c.
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

/* If a copy is generated on all paths to a block,
 * and its source is updated on one path,
 * it doesn't reach that block
 * */


int f(int src, int flag) {
    int x = src;  // generate x = src
    if (flag) {
        src = 65;  // kill x = src
    }
    wacc_emit_char(src);  // use src so assignment doesn't get optimized away entirely
    return x;      // make sure we don't rewrite this as 'return src'
}

int wacc_program_main(void) {
    // first call f with flag = 0;
    // validate return value, and make sure
    // src is not updated
    if (f(68, 0) != 68) {
        return 1;
    }

    // now call f with flag = 1;
    // validate return value and make sure
    // src is updated
    if (f(70, 1) != 70) {
        return 2;
    }

    return 0;  // success
}

int main(void) {
    const char *expected_output = "DA";
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
