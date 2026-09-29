/* Adapted from WACC chapter 18 static_structs.c. Record the original
 * output in memory; use static objects where the source used libc malloc.
 * Check every byte of state observed across calls and through pointers. */
#define WACC_EXPECTED_LENGTH 41
#define WACC_OUTPUT_CAPACITY WACC_EXPECTED_LENGTH
static char wacc_output[WACC_OUTPUT_CAPACITY];
static int wacc_output_length;
static int wacc_output_overflow;

int wacc_emit_char(int ch) {
    if (wacc_output_length == WACC_OUTPUT_CAPACITY)
        wacc_output_overflow = 1;
    else {
        wacc_output[wacc_output_length] = (char)ch;
        wacc_output_length = wacc_output_length + 1;
    }
    return ch;
}

int wacc_emit_string(char *text) {
    int length = 0;
    while (text[length]) {
        wacc_emit_char(text[length]);
        length = length + 1;
    }
    wacc_emit_char('\n');
    return length + 1;
}

// test that changes to static struct are retained across function calls
// do this by validating text captured in memory,
// instead of usual pattern of signifying success/failure with return value
void test_static_local(int a, int b) {
    struct s {
        int a;
        int b;
    };

    static struct s static_struct;
    if (!(static_struct.a || static_struct.b)) {
        wacc_emit_string("zero");
    } else {
        wacc_emit_char(static_struct.a);
        wacc_emit_char(static_struct.b);
        wacc_emit_char('\n');
    }

    static_struct.a = a;
    static_struct.b = b;
}

// test that changes to struct made through static pointer are retained across
// function calls do this by validating text captured in memory
void test_static_local_pointer(int a, int b) {
    struct s {
        int a;
        int b;
    };

    static struct s *struct_ptr;
    if (!struct_ptr) {
        static struct s allocated;
        struct_ptr = &allocated;
    } else {
        wacc_emit_char(struct_ptr->a);
        wacc_emit_char(struct_ptr->b);
        wacc_emit_char('\n');
    }

    struct_ptr->a = a;
    struct_ptr->b = b;
}

// test that changes to global struct are visible across function calls
struct global {
    char x;
    char y;
    char z;
};

struct global g;

void f1(void) {
    g.x = g.x + 1;
    g.y = g.y + 1;
    g.z = g.z + 1;
}

void f2(void) {
    wacc_emit_char(g.x);
    wacc_emit_char(g.y);
    wacc_emit_char(g.z);
    wacc_emit_char('\n');
}

void test_global_struct(void) {
    g.x = 'A';
    g.y = 'B';
    g.z = 'C';

    f1();
    f2();
    f1();
    f2();
}

// test that changes to global struct pointer are visible across function calls
struct global *g_ptr;

void f3(void) {
    g_ptr->x = g_ptr->x + 1;
    g_ptr->y = g_ptr->y + 1;
    g_ptr->z = g_ptr->z + 1;
}

void f4(void) {
    wacc_emit_char(g_ptr->x);
    wacc_emit_char(g_ptr->y);
    wacc_emit_char(g_ptr->z);
    wacc_emit_char('\n');
}

void test_global_struct_pointer(void) {
    g_ptr = &g;  // first, point to global struct from previous test
    f3();
    f4();
    f3();
    f4();
    // now declare a new struct and point to that instead
    static struct global allocated;
    g_ptr = &allocated;
    g_ptr->x = 'a';
    g_ptr->y = 'b';
    g_ptr->z = 'c';
    f3();
    f4();
    f3();
    f4();
}

int wacc_program_main(void) {
    test_static_local('m', 'n');
    test_static_local('o', 'p');
    test_static_local('!', '!');
    ;  // last one, won't be printed
    test_static_local_pointer('w', 'x');
    test_static_local_pointer('y', 'z');
    test_static_local_pointer('!', '!');
    ;  // last one, won't be printed
    test_global_struct();
    test_global_struct_pointer();
    return 0;
}

int main(void) {
    const char *expected = "zero\nmn\nop\nwx\nyz\nBCD\nCDE\nDEF\nEFG\nbcd\ncde\n";
    int result = wacc_program_main();
    if (result != 0) return 1;
    if (wacc_output_overflow || wacc_output_length != WACC_EXPECTED_LENGTH) return 2;
    for (int i = 0; i < WACC_EXPECTED_LENGTH; i = i + 1) {
        if (wacc_output[i] != expected[i]) return 3;
    }
    return 0;
}
