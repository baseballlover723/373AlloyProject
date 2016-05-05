module M2/RDT20

open util/ordering[State]

sig State {
	sender: one Sender,
	receiver: one Receiver,
	currentState: one StateType,
	packet: one Packet
}

abstract sig StateType {}
one sig SendSendState extends StateType {}
one sig SendWaitState extends StateType {}
one sig ReceiveState extends StateType {}

abstract sig DataState {}
one sig Valid extends DataState {}
one sig Corrupt extends DataState {}

abstract sig Stream {
	buffer: set Data
}


sig Sender extends Stream {}
sig Receiver extends Stream {}

sig Packet {
	data: one Data,
	checksum: one DataState
}

sig Data {}

fact Reliable {
	no d: Data | d not in Sender.buffer + Receiver.buffer
}


// makes sure the first state is sending and waiting for data
pred Init[s: State] {
	s.currentState = SendSendState
	some s.sender.buffer
	no s.receiver.buffer
}

// ends when the sender has sent all of its data to the receiver
pred End[s: State] {
	first.sender.buffer in s.receiver.buffer
	no s.sender.buffer
	last.packet.checksum = Valid
	last.prev.packet.checksum = Valid
}

pred Transition[s: State] {
	// if the current state is sss, we send the data
	s.currentState = SendSendState => SendTransition[s]
	// if the current state is sws, we wait to see if data was corrupted
	s.currentState = SendWaitState => WaitTransition[s]
	// if the current state is rs, we receive the data
	s.currentState = ReceiveState => ReceiveTransition[s]
}

pred SendTransition[s: State] {
	// if the packet is corrupt, then the received packet has to be corrupt
	s.packet.checksum = Corrupt => s.next.packet.checksum = Corrupt
	// sends one data
	one d: s.sender.buffer | RdtSend[s, d]

}

pred RdtSend[s: State, d: Data] {
	// send the data after making the it into a packet
	UdtSend[s, MakePacket[d]]
}

fun MakePacket[d: Data]: Packet {
	// make the data into a packet
	{p: Packet | p.data = d }
}

pred UdtSend[s: State, p:Packet] {
	// makes sure the dat is the same, but doesn't make sure that the packet is still valid
	s.packet.data = p.data
	s.next.packet.data = p.data
	s.next.next.packet.data = p.data
}


pred ReceiveTransition[s: State] {
	//s.packet.data = s.prev.packet.data
	// if the packet is valid, it should stay valid for wait. if the packet is corrupt, it should stay corrupt for wait
	//s.next.packet.checksum = s.packet.checksum
	// the sender buffer shouldn't change until the data is verified to be valid in wait
	s.sender.buffer = s.prev.sender.buffer
	// if it is valid, then receive the data
	s.packet.checksum = Valid => RdtRcv[s, s.packet]
	// otherwise make sure the buffer doesn't change
	s.packet.checksum = Corrupt => s.receiver.buffer = s.prev.receiver.buffer

}

pred RdtRcv[s: State, p: Packet] {
	DeliverData[s, Extract[p]]
}

fun Extract[p: Packet]: Data {
	// extract the data from the packet
	{p.data}
}

pred DeliverData[s: State, d: Data] {
	// make sure that the extracted data is added to the receiver's buffer
	s.receiver.buffer = s.prev.receiver.buffer + d
}

pred WaitTransition[s: State] {
	// make sure the checksum is the same
	s.packet.checksum = s.prev.packet.checksum
	// if the packet is valid, acknowledge
	s.packet.checksum = Valid => acknowledge[s]
	// else try to resend the data
	else resend[s]
}

pred resend[s: State] {
	// makes sure the packet is corrupt
	s.packet.checksum = Corrupt
	// the next sender's packet can be valid or corrupt
	s.next.packet.checksum = Valid or s.next.packet.checksum = Corrupt
	// makes sure that the sender buffer doesn't change
	s.sender.buffer = s.prev.sender.buffer
	// makes sure that the receiver buffer also doesn't change
	s.receiver.buffer = s.prev.receiver.buffer
	// make sure the next send's packet data is the same
	s.next.packet.data = s.packet.data

}

pred acknowledge[s: State] {
	// makes sure the packet is valid
	s.packet.checksum = Valid
	// make sure the buffer loses the sent data
	s.sender.buffer = s.prev.sender.buffer - s.packet.data
	// makes sure the receiver is the same as last
	s.receiver.buffer = s.prev.receiver.buffer
}

pred Progress[s: State] {
	//s not in s.^prev
}

pred CorrectNextState[s: State] {
	s.currentState = SendSendState => s.next.currentState = ReceiveState
	s.currentState = ReceiveState => s.next.currentState = SendWaitState
	s.currentState = SendWaitState => s.next.currentState = SendSendState

}

pred Trace {
	first.Init
	all s: State - last |
		Transition[s] and Progress[s] and CorrectNextState[s]
}

pred WinTrace {
	Trace and last.End	
}

assert transferAllData {
	Trace[] => last.End[]
}

run WinTrace for 6 State, 2 Data, 6 Stream, 6 Packet
check transferAllData for 3 State, 1 Data, 10 Stream, 1 Packet
