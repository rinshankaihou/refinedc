//@rc::inlined
//@ Notation F_SETFL := 4 (only parsing).
//@ Notation O_NONBLOCK := 2048 (only parsing).
//@rc::end


[[rc::args("int<i32>", "{F_SETFL} @ int<i32>","{O_NONBLOCK} @ int<i32>")]]
[[rc::returns("{0} @ int<i32>")]]
int fcntl(int fildes, int cmd, int flag);
