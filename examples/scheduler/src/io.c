#include <errno.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/udp.h>

int open_udp_socket(int port_number) {
  struct sockaddr_in addr = {0};

  // open the socket
  int the_socket = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
  if (the_socket < 0) {
    perror("socket creation");
    return the_socket;
  }

  /* what interface to listen on -- we simply listen on all
     interfaces available */
  int host_addr = INADDR_ANY;

  // bind it to the given host and port
  addr.sin_family = AF_INET;
  addr.sin_port = htons(port_number);
  addr.sin_addr.s_addr = htonl(host_addr);
  int err = bind(the_socket, (struct sockaddr*) &addr, sizeof(addr));
  if (err < 0) {
    perror("binding to port");
    return err;
  }

  return the_socket;
}

/* create a copy of the STDIN file descriptor */
int open_stdin(void) {
  /* duplicate STDIN file descriptor so we can later mark it nonblocking */
  int fd = dup(fileno(stdin));
  return fd;
}

