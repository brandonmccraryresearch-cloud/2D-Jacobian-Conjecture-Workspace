import Jacobian.ChartProof.Reflect

set_option pp.explicit true in
example {L : Type*} [Field L] [CharZero L] (x : L) (h : (123456789012345678901234567890 : L) * x = 0) : True := by
  trace_state
  trivial

set_option profiler true in
set_option trace.Meta.synthInstance true in
example {L : Type*} [Field L] [CharZero L] (x : L) (h : (923456789012345678901234567891 : L) * x = 0) : True := trivial
