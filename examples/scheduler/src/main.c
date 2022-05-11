#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>

#include "fdsched.h"
#include "io.h"

// the two arbitrary port numbers the task will be activated by
#define UDP_LISTEN_PORT1 2006
#define UDP_LISTEN_PORT2 1619

/* the kinds of messages we are going to handle */
enum message_types {
  MSG_FOO,
  MSG_BAR,
  MSG_SLEEP,
  MSG_EXIT,
  MSG_GARBAGE, /* anything else */
};

/* make up some arbitrary priorities (lower number <-> higher priority) */
#define FOO_PRIO   27
#define BAR_PRIO   10
#define SLEEP_PRIO  1
#define EXIT_PRIO   2
#define GARBAGE_PRIO 100

/* the message handler callbacks */
static int on_foo(struct message* msg);
static int on_bar(struct message* msg);
static int on_sleep(struct message* msg);
static int on_termination(struct message* msg);
static int on_garbage(struct message* msg);

int main(int argc, char** argv) {
  struct fd_scheduler fds;
  int fd;

  fds_init(&fds);

  /* open channels */
  fd = open_udp_socket(UDP_LISTEN_PORT1);
  if (fd < 0)
    perror("cannot open UDP socket");
  fds_add_channel(&fds, fd);

  fd = open_udp_socket(UDP_LISTEN_PORT2);
  if (fd < 0)
    perror("cannot open UDP socket");
  fds_add_channel(&fds, fd);

  fd = open_stdin();
  if (fd < 0)
    perror("cannot open stdin");
  fds_add_channel(&fds, fd);

  /* add callbacks */
  fds_set_callback(&fds, MSG_FOO, on_foo, FOO_PRIO);
  fds_set_callback(&fds, MSG_BAR, on_bar, BAR_PRIO);
  fds_set_callback(&fds, MSG_SLEEP, on_sleep, SLEEP_PRIO);
  fds_set_callback(&fds, MSG_EXIT, on_termination, EXIT_PRIO);
  fds_set_callback(&fds, MSG_GARBAGE, on_garbage, GARBAGE_PRIO);

  printf("Starting the NP-FP FD scheduler...\n");
  return fds_run(&fds);
}

/* application-specific message identification function */
message_type_t message_identify_type(struct message *msg) {
  if (msg->len < 3) {
    return MSG_GARBAGE;
  }

  if (!memcmp("FOO", msg->data, 3) || !memcmp("foo", msg->data, 3)) {
    return MSG_FOO;
  } else if (!memcmp("BAR", msg->data, 3) || !memcmp("bar", msg->data, 3)) {
    return MSG_BAR;
  } else if (!memcmp("ZZZ", msg->data, 3) || !memcmp("zzz", msg->data, 3)) {
    return MSG_SLEEP;
  } else if (!memcmp("XXX", msg->data, 3) || !memcmp("xxx", msg->data, 3)) {
    return MSG_EXIT;
  } else {
    return MSG_GARBAGE;
  }
}

static int on_foo(struct message* msg) {
  printf("[II] received a FOO message consisting of %ld bytes!\n", msg->len);
  return 0;
}

static int on_bar(struct message* msg) {
  printf("[II] received a BAR message consisting of %ld bytes!\n", msg->len);
  return 0;
}

static int on_sleep(struct message* msg) {
  printf("Zzzz... Blocking for %ld seconds to simulate work\n", msg->len);
  sleep((int) msg->len);
  return 0;
}

static int on_termination(struct message* msg) {
  printf("[!!] terminating.\n");
  return 1;
}

static int on_garbage(struct message* msg) {
  printf("[??] received %ld bytes of garbage\n", msg->len);
  return 0;
}

