@R0
D = M

@max
M = D

@i
M = 1

(LOOP_START)
	@i
	D = M

	@4
	D = D - A

	@LOOP_END
	D; JGT

	@i
	A = M
	D = M

	@max
	D = D - M

	@NOT_MAX
	D; JLE

	@i
	A = M
	D = M

	@max
	M = D

	(NOT_MAX)

	@i
	M = M + 1

	@LOOP_START
	0; JMP

(LOOP_END)

@max
D = M

@R5
M = D

(END)
@END
0; JMP