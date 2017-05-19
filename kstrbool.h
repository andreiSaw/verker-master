#ifndef KSTRBOOL_H
#define KSTRBOOL_H

#include "kernel_definitions.h"
#include "ctype.h"

/*@ axiomatic kstrtobool {
     predicate kstrtobool_fmt_false(char *s) =
       tolower(s[0]) == 'n' || s[0] == '0' ||
       (tolower(s[0]) == 'o' && tolower(s[1]) == 'f');

     predicate kstrtobool_fmt_true(char *s) =
       tolower(s[0]) == 'y' || s[0] == '1' ||
       (tolower(s[0]) == 'o' && tolower(s[1]) == 'n');

     predicate kstrtobool_fmt(char *s) =
       kstrtobool_fmt_true(s) ||
       kstrtobool_fmt_false(s);
    }
 */

/**
 * kstrtobool - convert common user inputs into boolean values
 * @s: input string
 * @res: result
 *
 * This routine returns 0 iff the first character is one of 'Yy1Nn0', or
 * [oO][NnFf] for "on" and "off". Otherwise it will return -EINVAL.  Value
 * pointed to by res is updated upon finding a match.
 */

/*@ requires s == \null || \valid(s) && (tolower(*s) == 'o' ==> \valid(s+1));
    requires \valid(res);
    ensures \result == 0 || \result == -EINVAL;
    ensures \result == -EINVAL ==> res == \old(res);
    behavior INVAL:
       assumes s == \null || !kstrtobool_fmt(s);
       assigns \nothing;
       ensures \result == -EINVAL;
    behavior CORRECT:
       assumes s != \null && kstrtobool_fmt(s);
       assigns *res;
       ensures kstrtobool_fmt_true(s)  ==> *res == 1;
       ensures kstrtobool_fmt_false(s) ==> *res == 0;
       ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
 */
int kstrtobool(const char *s, bool *res);

#endif
