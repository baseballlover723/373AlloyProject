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
	checksum: DataState
}

sig Data {}

fact Reliable {
	no d: Data | d not in Sender.buffer + Receiver.buffer
}


fact Convience {
	//#Sender = #Receiver
	//#Stream = 2.mul[#State]
}

pred Init[s: State] {
	s.currentState = SendSendState
	some s.sender.buffer
	s.packet.checksum = Valid or s.packet.checksum = Corrupt
}

pred End[s: State] {
	first.sender.buffer in s.receiver.buffer
	no s.sender.buffer
}

pred Transition[s: State] {
	s.currentState = SendSendState => SendTransition[s]
	s.currentState = SendWaitState => WaitTransition[s]
	s.currentState = ReceiveState => ReceiveTransition[s]
}

pred SendTransition[s: State] {
	s.packet.checksum = Corrupt => s.next.packet.checksum = Corrupt
	one d: s.sender.buffer | RdtSend[s, d]
	
}

pred RdtSend[s: State, d: Data] {
	UdtSend[s, MakePacket[d]]
}

fun MakePacket[d: Data]: Packet {
	{p: Packet | p.data = d }
}

pred UdtSend[s: State, p:Packet] {
	s.packet.data = p.data
	s.next.packet.data = p.data
	s.next.next.packet.data = p.data
}


pred ReceiveTransition[s: State] {
	s.packet.checksum = s.next.packet.checksum
	s.sender.buffer = s.prev.sender.buffer	
	s.packet.checksum = Valid => 
		RdtRcv[s, s.packet]
	else s.receiver.buffer = s.prev.receiver.buffer

}

pred RdtRcv[s: State, p: Packet] {
	DeliverData[s, Extract[p]]
}

fun Extract[p: Packet]: Data {
	{p.data}
}

pred DeliverData[s: State, d: Data] {
	s.receiver.buffer = s.prev.receiver.buffer + d
}

pred WaitTransition[s: State] {
	s.packet.checksum = Valid => acknowledge[s]
	else
	resend[s]
	//else acknowledge[s]
}

pred resend[s: State] {
	s.packet.checksum = Corrupt
	s not = last => s.next.packet.checksum = Valid or s.next.packet.checksum = Corrupt
	s.sender.buffer = s.prev.sender.buffer
	s.receiver.buffer = s.prev.receiver.buffer
	s not = last => s.next.packet.data = s.packet.data
	s not = last => s.next.packet not = s.packet
}

pred acknowledge[s: State] {
	s.packet.checksum = Valid
	s.sender.buffer = s.prev.sender.buffer - s.packet.data
	s not = last => s.sender.buffer = s.next.sender.buffer
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
	all s: State |
		Transition[s] and Progress[s] and CorrectNextState[s]
}

pred FortheA {
	Trace[] and last.End[]
}

assert transferAllData {
	Trace => last.End
}

run FortheA for 3 State, 1 Data, 12 Stream, 2 Packet
check transferAllData for 3 State, 2 Data, 10 Stream, 2 Packet
