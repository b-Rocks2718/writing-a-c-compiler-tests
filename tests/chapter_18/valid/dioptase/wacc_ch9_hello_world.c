/*
 * Adapted from WACC chapter_9/valid/arguments_in_registers/hello_world.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the original program's
 * return value and control flow remain under test.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 14
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


int wacc_program_main(void) {
    wacc_emit_char(72);
    wacc_emit_char(101);
    wacc_emit_char(108);
    wacc_emit_char(108);
    wacc_emit_char(111);
    wacc_emit_char(44);
    wacc_emit_char(32);
    wacc_emit_char(87);
    wacc_emit_char(111);
    wacc_emit_char(114);
    wacc_emit_char(108);
    wacc_emit_char(100);
    wacc_emit_char(33);
    wacc_emit_char(10);
    // The source main implicitly returned zero; preserve that after wrapping.
    return WACC_EXPECTED_RETURN;
}

int main(void) {
    const char *expected_output = "Hello, World!\n";
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
