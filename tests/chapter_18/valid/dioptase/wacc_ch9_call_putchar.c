/*
 * Adapted from WACC chapter_9/valid/stack_arguments/call_putchar.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the original program's
 * return value and control flow remain under test.
 */
#define WACC_EXPECTED_RETURN 8
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

#ifdef SUPPRESS_WARNINGS
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

/* Make sure we can correctly manage calling conventions from the callee side
 * (by accessing parameters, including parameters on the stack) and the caller side
 * (by calling a standard library function) in the same function
 */
int foo(int a, int b, int c, int d, int e, int f, int g, int h) {
    wacc_emit_char(h);
    return a + g;
}

int wacc_program_main(void) {
    return foo(1, 2, 3, 4, 5, 6, 7, 65);
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
