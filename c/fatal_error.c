#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

// both of these functions are from hardened_malloc, util.c file

static int write_full(int fd, const char *buf, size_t length) {
    do {
        ssize_t bytes_written = write(fd, buf, length);
        if (bytes_written == -1) {
            if (errno == EINTR) {
                continue;
            }
            return -1;
        }
        buf += bytes_written;
        length -= bytes_written;
    } while (length);

    return 0;
}

void fatal_error(const char *s) {
  const char *prefix = "fatal allocator error: ";
  (void)(write_full(STDERR_FILENO, prefix, strlen(prefix)) != -1 &&
    write_full(STDERR_FILENO, s, strlen(s)) != -1 &&
    write_full(STDERR_FILENO, "\n", 1));
  abort();
}
