#include <assert.h>
#include <errno.h>
#include <stdlib.h>

#include "sys/system.h"
#include "fdsched.h"

static
int nop_callback(struct message* _) {
  return 0;
}

void fds_init(struct fd_scheduler* fds) {
  fds->num_channels = 0;
  // TODO: RefinedC currently does not accept the following:
  /* fds->sched.prio_levels = (prio_bitmap_t) { 0 }; */
  prio_level_init(&fds->sched.prio_levels);
  for(int typ = 0; typ < NUM_MESSAGE_TYPES; typ += 1) {
    fds->sched.callbacks[typ] = (struct callback) {0, nop_callback};
  }
  for(int prio = 0; prio < NUM_PRIORITIES; prio += 1) {
    fds->sched.pending[prio] = (struct message_queue) {NULL, NULL};
  }
}

int fds_add_channel(struct fd_scheduler* fds, int fd) {
  assert(fds->num_channels < MAX_INPUT_CHANNELS);

  /* mark as nonblocking */
  int err = fcntl(fd, F_SETFL, O_NONBLOCK);
  if (err)
    return err;

  fds->input_channels[fds->num_channels].fd = fd;
  fds->input_channels[fds->num_channels].events = POLLIN;
  fds->num_channels++;

  return 0;
}

void fds_set_callback(struct fd_scheduler* fds,
           message_type_t type, callback_fn_t f, priority_t prio) {
  fds->sched.callbacks[type] = (struct callback) {prio, f};
}

static
void wait_for_input(struct fd_scheduler* fds) {
  int err;

  /* Wait for data to become available, ignoring spurious
     wake-ups due to signals. */
  do {
    err = poll(fds->input_channels, fds->num_channels, -1);
  } while (err < 0);
}

static
int receive_one_message(struct fd_scheduler* fds, int fd) {
  /* NB: we really should use pre-allocated memory here to avoid page faults */
  struct message *msg = malloc(sizeof(*msg));

  /* we are not going to handle memory allocation failures */
  assert(msg);

  /* receive data from FD */
  int n = read(fd, &msg->data, MAX_MESSAGE_LEN);

  if (n <= 0) {
    // FIXME: should handle closed FDs gracefully
    free(msg);
    return n;
  } else {
    msg->len = n;
    npfp_enqueue(&fds->sched, msg);
    return 0;
  }
}

static
int receive_messages(struct fd_scheduler* fds, int fd) {
  int err;
  do {
    err = receive_one_message(fds, fd);
  } while (!err);

  if (errno == EWOULDBLOCK || errno == EAGAIN)
    /* nothing else to receive for now, this is fine */
    return 0;
  else
    return err;
}

static
int check_channels(struct fd_scheduler* fds) {
  int err;
  for (nfds_t ch = 0; ch < fds->num_channels; ch++) {
    if (fds->input_channels[ch].revents) {
      err = receive_messages(fds, fds->input_channels[ch].fd);
      if (err < 0)
        return err;
    }
  }
  return 0;
}

int fds_run(struct fd_scheduler* fds) {
  int err;

  assert(fds->num_channels > 0);

  while (1) {
    wait_for_input(fds);
    do {
      /* receive messages on all channels */
      err = check_channels(fds);
      if (err)
        return err;

      /* get the highest-priority message */
      struct message *msg = npfp_dequeue(&fds->sched);

      /* if there is no message, wait for new input */
      if (!msg)
        break;

      /* consume the message */
      err = npfp_dispatch(&fds->sched, msg);

      /* release the memory */
      free(msg);

      /* terminate if the callback failed for some reason */
      if (err)
        return err;
    } while (!err);
  }
}
