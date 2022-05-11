#pragma once

#include <stdint.h>

#if defined(__refinedc__)
typedef int64_t ssize_t;

#define F_SETFL    4
#define O_NONBLOCK    04000
#define POLLIN    0x001

/* Type used for the number of file descriptors.  */
typedef unsigned long int nfds_t;
/* Data structure describing a polling request.  */
struct pollfd
  {
    int fd;      /* File descriptor to poll.  */
    short int events;    /* Types of events poller cares about.  */
    short int revents;    /* Types of events that actually occurred.  */
  };

// TODO: RefinedC does not understand ... so we use the concrete prototype that we use
/* extern int fcntl (int __fd, int __cmd, ...); */
extern int fcntl (int __fd, int __cmd, int __val);
extern int poll (struct pollfd *__fds, nfds_t __nfds, int __timeout);
extern ssize_t read (int __fd, void *__buf, size_t __nbytes);

#else

#include <poll.h>
#include <fcntl.h>
#include <unistd.h>

#endif
