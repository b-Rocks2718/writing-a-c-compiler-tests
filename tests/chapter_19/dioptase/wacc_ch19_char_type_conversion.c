/*
 * Adapted from WACC chapter_19/copy_propagation/all_types/char_type_conversion.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the optimizer behavior and
 * the original program's return value remain under test.
 */
#define WACC_EXPECTED_RETURN 1
#define WACC_EXPECTED_LENGTH 4
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

/* Test that we can propagate copies between char and signed char */
#ifdef SUPPRESS_WARNINGS
#ifdef __clang__
#pragma clang diagnostic ignored "-Wconstant-conversion"
#else
#pragma GCC diagnostic ignored "-Woverflow"
#endif
#endif


void print_some_chars(char a, char b, char c, char d) {
    wacc_emit_char(a);
    wacc_emit_char(b);
    wacc_emit_char(c);
    wacc_emit_char(d);
}

int callee(char c, signed char s) {
    return c == s;
}

int target(char c, signed char s) {
    // first, call another function, with these arguments
    // in different positions than in target or callee, so we can't
    // coalesce them with the param-passing registers or each other
    print_some_chars(67, 66, c, s);

    s = c;  // generate s = c - we can do this because for the purposes of copy
            // propagation, we consider char and signed char the same type

    // both arguments to callee should be the same
    return callee(s, c);
}

int wacc_program_main(void) {
    return target(65, 64);
}

int main(void) {
    const char *expected_output = "CBA@";
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
