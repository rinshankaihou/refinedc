#pragma once

//@rc::import fdsched_extra from refinedc.examples.scheduler.src.fdsched

//@rc::context `{!PacketArrivals}

//@rc::inlined
//@Definition read_update_log (t : nat) (l : list LogEntry) (fd : FD) : list LogEntry := l ++ (from_option (λ ID, [read_from_socket ID t]) [] (get_head_ID_option t l fd)).
//@rc::end

[[rc::parameters("data : {list Z}", "fd : Z", "l : loc", "log : {list LogEntry}","t1 : nat")]]
[[rc::exists("t2 : nat")]]
[[rc::args("fd @ int<i32>", "l @ &own<{uninit (mk_array_layout u8 (Z.to_nat max_msg_len))}>", "max_msg_len @ int<u64>")]]
[[rc::returns("{if (bool_decide (is_Some (get_head_ID_option t1 log fd))) then max_msg_len else -1} @ int<i64>")]]
// read requires the current log and the current time
[[rc::requires("[curr_time t1]")]]
[[rc::requires("[curr_log log]")]]
//the timing and the log is updated
[[rc::ensures("[curr_time t2]")]]
[[rc::ensures("[curr_log (read_update_log t2 log fd)]")]]
[[rc::ensures("{t2 = t1}")]]
[[rc::ensures("own l : array_p<u8, {get_packet_data_option (get_head_ID_option t1 log fd) `at_type` int(u8)},"
	      "{Z.to_nat max_msg_len}>")]]
ssize_t read(int fd, void* data, size_t msg_len);
