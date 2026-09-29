/*
 * Adapted from WACC chapter_18/valid/extra_credit/semantic_analysis/union_self_pointer.c.
 * Replace one use of unsupported long with int. The self-referential union pointer and equality assertion remain unchanged.
 */
// A union type can't have itself as a member but can have a pointer
// to itself as a member
union self_ptr {
    union self_ptr *ptr;
    int l;
};

int main(void) {
    union self_ptr u = {&u};
    if (&u != u.ptr) {
        return 1; // fail
    }
    return 0;
}