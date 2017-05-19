#include "strcspn.h"

/*@ requires valid_str(s);
		requires valid_str(reject);
		assigns \nothing;
		ensures \forall char *z; s <= z < s + strlen(s) ==> \exists char *t; reject <= t < reject + strlen(reject) &&
			*z == *t;
	  ensures \result == strcspn(s, reject);
 */
size_t strcspn(const char *s, const char *reject)
{
	const char *p;
	const char *r;
	size_t count = 0;
  /*@
      loop invariant 0 <= count <= strlen(s);
			loop invariant count == p - s;
      loop invariant s <= p <= s + strlen(s);
			loop invariant \forall char *z; s <= z < p ==>
										(\exists char *t; reject <= t < reject + strlen(reject) && *z == *t);
      loop variant strlen(s) - (p - s);
 */
	for (p = s; *p != '\0'; ++p) {
    /*@
				loop invariant reject <= r <= reject + strlen(reject);
				loop invariant \forall char *t; reject <= t < r ==> *p != *t;
        loop variant strlen(reject) - (r - reject);
    */
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r)

				return count;
		}

		++count;

	}
	return count;
}

int main(void)
{
    printf("%d\n", strcspn("123", "4"));
    return 0;
}
