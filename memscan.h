#ifndef __MEMSCAN_H__
#define __MEMSCAN_H__

#include "kernel_definitions.h"

/**
 * memscan - Find a character in an area of memory.
 * @addr: The memory area
 * @c: The byte to search for
 * @size: The size of the area.
 *
 * returns the address of the first occurrence of @c, or 1 byte past
 * the area if @c is not found
 */

/*@ requires \typeof(addr) <: \type(u8 *);
    requires \valid((u8 *)addr+(0..size-1));
    assigns \nothing;
    ensures \base_addr(addr) == \base_addr(\result);
    ensures addr <= \result <= addr + size;
    behavior found:
       assumes \exists integer i; 0 <= i < size && ((u8 *)addr)[i] == c;
       ensures \exists integer i; 0 <= i < size &&
               (\forall integer j; 0 <= j < i ==> ((u8 *)addr)[j] != c) &&
               ((u8 *)addr)[i] == c &&
               \result == addr + i;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < size ==> ((u8 *)addr)[i] != c;
       ensures \result == addr + size;
    complete behaviors;
    disjoint behaviors;
 */
void *memscan(void *addr, int c, size_t size);

#endif // __MEMSCAN_H__
