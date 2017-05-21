#include "strspn.h"

size_t strspn(const char*s, const char*accept)
{
    const char*p;
    const char*a;
    size_t count = 0;

    /*@ loop invariant s <= p <= s + strlen(s);
        loop invariant 0 <= count <= strlen(s);
        loop invariant count == p - s;
        loop invariant \forall char *z; s <= z < p ==>
                    (\exists char *t; accept <= t < accept + strlen(accept) && *z == *t);
        loop invariant strspn(s, accept) == strspn(p, accept) + count;
        loop variant (strlen(s) - (p-s));
    */
    for (p = s; *p != '\0'; ++p)
    {
    /*@ loop invariant accept <= a <= accept + strlen(accept);
        loop invariant \forall char *t; accept <= t < a ==> *p != *t;
        loop variant strlen(accept) - (a - accept);
    */
        for (a = accept; *a != '\0'; ++a)
        {
            if (*p == *a)
                break;
        }
        //@ assert *a != '\0' ==> in_array(accept, *p);
        // assert *a != '\0' ==> \exists char *t; accept <= t < accept + strlen(accept) && *t == *p;
        if (*a == '\0')
            //@assert !in_array(accept, *p);
            return count;
        ++count;
    }
    return count;
}
