/* Source: https://cvsweb.openbsd.org/cgi-bin/cvsweb/~checkout~/src/lib/libc/string/strlen.c */
/* copyright and version comments removed */

#include <string.h>

size_t
strlen(const char *str)
{
	const char *s;

	for (s = str; *s; ++s)
		;
	return (s - str);
}

/* commented out as irrelevant */
/*DEF_STRONG(strlen);*/
