module M1/RDT10

open util/ordering[State]

sig State {
	sender: one Sender,
	receiver: one Receiver
}

abstract sig Stream {
	buffer: set Data
}
sig Sender extends Stream {}
sig Receiver extends Stream {}

sig Data {}

fact Reliable {
	no d: Data | d not in Sender.buffer + Receiver.buffer
}

fact Convience {
	#Sender = #Receiver
	#Stream = 2.mul[#State]
}

pred Init[s: State] {
	#sender.buffer > 0
}

pred End[s: State] {
	first.sender.buffer in s.receiver.buffer
	#s.sender.buffer = 0
}

pred Transition[s, s': State] {
	one d: s.sender.buffer |
		RdtSend[s, s', d] and
		RdtRcv[s, s', d]
}

pred RdtSend[s, s': State, d: Data] {
	UdtSend[s, s', d]
}

fun MakePacket[d: Data]: Data {
	{d}
}

pred UdtSend[s, s': State, p: Data] {
	s'.sender.buffer = {s.sender.buffer - p}
}

pred RdtRcv[s, s': State, d: Data] {
	DeliverData[s, s', Extract(d)]
}

fun Extract[d: Data]: Data {
	{d}
}

pred DeliverData[s, s': State, d: Data] {
	s'.receiver.buffer = s.receiver.buffer + d
}

pred Trace {
	first.Init
	all s: State-last |
		let s' = s.next |
			Transition[s, s']
	//last.End
}

run Trace for 3 State, 2 Data, 10 Stream
run Init for 1 State, exactly 5 Data
run End for 1 State, exactly 5 Data

