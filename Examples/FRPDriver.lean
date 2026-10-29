import Applications.FRP.DriverIO

/-! Checked codec applications and lifecycle boundaries for the external driver. -/
namespace Examples.FRPDriver
open FRPSpec.Frontier FRPSpec.Frontier.Driver

/-- Duplicate timestamps and an empty fragment are genuine wire inputs. -/
def fragmented : Command := .source .left ⟨1,[(0,[7]),(0,[]),(0,[8])]⟩
example : encode fragmented = [2,0,1,3,0,1,7,0,0,0,1,8] := by decide
example : decodeBounded (encode fragmented) = .ok fragmented :=
  decodeBounded_encode fragmented (by decide)
example : decodePacket 3 (encodePacket [(0,[7]),(0,[]),(0,[8])] ++ [99]) =
    some ([(0,[7]),(0,[]),(0,[8])],[99]) := decodePacket_encode [(0,[7]),(0,[]),(0,[8])] [99]
example : decodeBounded [2,0,1,1,0,2,7] = .error .malformed := by decide
example : decodeBounded [0,65536,0] = .error .limit := by decide
example : decodeBounded [0,0,65535] = .error .limit := by decide
example : decodeBounded [0,0,65534] = .ok (.begin 0 65534) := by decide
example : (decodedStep Driver.initial (.error .malformed)).1 = Driver.initial :=
  decoded_error_stutters Driver.initial .malformed

def commands : List Command :=
  [.begin 65535 0,fragmented,.source .right ⟨1,[]⟩,.process 0,.process 65535]
def result := replay Driver.initial (commands.map Except.ok)
example : result.2 =
    ["ok packet - status accepted response - aggregate -",
     "ok packet accepted status - response - aggregate -",
     "ok packet accepted status - response - aggregate -",
     "ok packet - status - response - aggregate -",
     "ok packet - status - response 65535 0 2 7 8 aggregate 1 15"] := by decide
example : result.1.consumer = (1,15) := by decide
example : (decodedStep result.1 (decodeBounded [0,0,0])).2 =
    "ok packet - status stale response - aggregate -" := by decide
example : (decodedStep result.1 (decodeBounded [0,65536,0])).1 = result.1 :=
  decoded_error_stutters result.1 .limit
example : decodeResponse (encodeResponse ⟨65535,0,[7,8]⟩ ++ [42]) =
    some (⟨65535,0,[7,8]⟩,[42]) := decodeResponse_encode _ _
example : decodeResponse (encodeResponse ⟨0,0,[]⟩) = some (⟨0,0,[]⟩,[]) :=
  decodeResponse_encode _ []
example : decodeAggregate (encodeAggregate (1,15)) = some (1,15) := decodeAggregate_encode _

example (tokens : List Nat) (c : Command) (h : decodeBounded tokens = .ok c) :
    supported c = true := decodeBounded_supported tokens c h
example (s : State) (xs : List (Except DecodeError Command)) :
    (replay s xs).1 = (Lifecycle.Pipeline.run Consumer s (acceptedCommands xs)).1 :=
  replay_state s xs
example (s : State) (c : Command) :
    ((step s c).1,(step s c).2.event) =
      Lifecycle.Pipeline.step (FRPSpec.Reactive.batches FRPSpec.Reactive.jointSpec) s c :=
  step_compiled s c
example : packetStatus result.1 (.source .left ⟨0,[]⟩) = some false := by decide
example : (step result.1 (.source .left ⟨0,[]⟩)).1 = result.1 :=
  rejected_stutters _ _ _ (by decide)
example : packetStatus Driver.initial fragmented =
    some ((advance (Driver.initial.lifecycle.engine.sources .left) 1 [(0,[7]),(0,[]),(0,[8])]).isSome) :=
  packet_status_agrees Driver.initial .left _

/-- No source silence advances a frontier; a complete empty window does. -/
example : (replay Driver.initial (([.begin 0 0,.process 0] : List Command).map Except.ok)).2 =
    ["ok packet - status accepted response - aggregate -",
     "ok packet - status - response - aggregate -"] := by decide
example : (replay Driver.initial (([.begin 0 0,.source .left ⟨1,[]⟩,
    .source .right ⟨1,[]⟩,.process 0] : List Command).map Except.ok)).1.consumer = (1,0) := by decide

end Examples.FRPDriver
