/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    lemma valid_str_shift1:
       \forall char *s;
       *s != '\0' &&
       valid_str(s) ==> valid_str(s+1);

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_str(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s;
          valid_str(s) ==> s[strlen(s)] == '\0';

    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_str(s) &&
          i <= strlen(s) ==>
          strlen(s+i) == strlen(s)-i;

    lemma strlen_shift_ex:
       \forall char *s, size_t i;
          valid_str(s) &&
          0 < i <= strlen(s) ==>
          strlen(s+i) < strlen(s);

    lemma strlen_shift1:
       \forall char *s;
          valid_str(s) && *s != '\0' ==>
          strlen(s) == 1 + strlen(s+1);

    lemma strlen_pointers:
       \forall char *s, *sc;
          valid_str(s)  &&
          valid_str(sc) &&
          \base_addr(s) == \base_addr(sc) &&
          s <= sc &&
          (\forall integer i; 0 <= i <= sc - s ==> s[i] != '\0') ==>
             strlen(sc) <= strlen(s);

    lemma strlen_main:
       \forall char *s, size_t n;
       valid_str(s) &&
       s[n] == '\0' &&
       (\forall size_t i; i < n ==> s[i] != '\0') ==>
           strlen(s) == n;
    }
 */
/*@ axiomatic StrSpn {

    //logic boolean in_array(char *s, char val) = *s == '\0' ? \false : (*s == val ? \true : in_array(s + 1, val));
    predicate in_array(char *s, char val) = \exists char *t; s <= t < s + strlen(s) && *t == val;

    //lemma in_array_shift1:
    //  \forall char* s, val; valid_str(s) && *s != '\0' && *s != val && val != '\0' ==>
    //  in_array(s, val) == in_array(s+1, val);

    //lemma in_array_at_null:
    //     \forall char* s, val;
    //      *s == '\0' && val != '\0' ==> in_array(s, val) == \false;

    //lemma in_array_shift2:
    //    \forall char* s, val; valid_str(s) && *s != '\0' && *s == val && val != '\0' ==>
    //        in_array(s, val) == \true;

logic size_t strspn(char*s, char*accept);
//= *s == '\0' ? (size_t)0 : (in_array(accept, *s) ? (size_t)1 + strspn(s + 1, accept) : strspn(s + 1, accept);

    lemma strspn_shift:
       \forall char *s,*accept;
          valid_str(s) && valid_str(accept) && *s != '\0' && in_array(accept,*s) ==>
          strspn(s, accept) == (size_t)1 + strspn(s+1, accept);

    lemma strspn_s_null:
       \forall char *s, *accept;
        *s == '\0' ==> strspn(s, accept) == (size_t)0;

        lemma strspn_accept_null:
           \forall char *s, *accept;
            *accept == '\0' ==> strspn(s, accept) == (size_t)0;

        lemma strspn_shift2:
           \forall char *s, *accept;
              valid_str(s) && valid_str(accept) && *s != '\0' && !in_array(accept,*s) ==>
              strspn(s, accept) == strspn(s + 1, accept);

        lemma strspn_shift3:
                 \forall char *s, *accept;
                    valid_str(s) && valid_str(accept) && *s == '\0' && in_array(accept,*s) ==>
                    strspn(s, accept) == (size_t)0;

        lemma strspn_pointers:
                          			 \forall char *s, *sc, *accept;
                          					valid_str(s)  && valid_str(sc) &&
                          					\base_addr(s) == \base_addr(sc) &&
                          					s <= sc < s + strlen(s)
                          					==> strspn(sc, accept) <= strspn(s, accept);

         lemma strspn_less:
                           				\forall char* s, *accept;
                           					valid_str(s) && valid_str(accept) && *s != '\0'
                           					==> strspn(s, accept) <= strlen(s);
        lemma strspn_exists:
        \forall char *p, *t, *s, *accept ; s <= p < s + strlen(s) &&  accept <= t < accept + strlen(accept) && *p == *t
                ==> \exists char *t; accept <= t < accept + strlen(accept) && s[strspn(s,accept)] == *t;
        lemma strspn_not:
        \forall char *p, *t, *s, *accept; s <= p < s + strlen(s) &&
                accept <= t < accept + strlen(accept) ==> *p != *t
                ==> strspn(s,accept) == strlen(s);
}
 */
 /*@ requires valid_str(s) && valid_str(accept);
     assigns \nothing;
     ensures 0 <= \result <= strlen(s);
     ensures \forall char *z; s <= z < s + strlen(s) ==>
                 \exists char *t; accept <= t < accept + strlen(accept) && *z == *t;
     ensures \result == strspn(s, accept);
 */
size_t strspn(const char *s, const char *accept);
