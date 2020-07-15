#pragma once

#include "../tutorial/alloc.h"

#define ALLOC(sz) alloc(sz)
#define FREE(sz,ptr) free(sz,ptr)
