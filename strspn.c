#include "strspn.h"
/*@ requires valid_str(s) && valid_str(accept);
    assigns \nothing;
    ensures 0 <= \result <= strlen(s);
*/
size_t strspn(const char*s, const char*accept)
{
    const char*p;
    const char*a;
    size_t count = 0;

    /*@ loop invariant s <= p <= s + strlen(s);
        loop invariant 0 <= count <= strlen(s);
        loop invariant count == p - s;
        loop variant (strlen(s) - (p-s));
    */
    for (p = s; *p != '\0'; ++p)
    {
    /*@ loop invariant accept <= a <= accept + strlen(accept);
        loop variant strlen(accept) - (a - accept);
    */
        for (a = accept; *a != '\0'; ++a)
        {
            if (*p == *a)
                break;
        }
        if (*a == '\0')
            return count;
        ++count;
    }
    return count;
}
