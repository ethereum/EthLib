module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.BeaconApi.Events

/-!
# Proofs: the topics and the messages of the event stream

Each topic has its own name, and the name gives the topic back.

A request of topics is read exactly when each name is that of a topic.

The stream holds, in order, the messages of the events whose topic the client chose.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

namespace EventTopic

/-- The name of a topic gives the topic back. -/
theorem ofName?_name (topic : EventTopic) : ofName? topic.name = some topic := by
  cases topic <;> rfl

/-- Two topics with one name are the same topic. -/
theorem name_injective : Function.Injective name := fun a b same => by
  simpa [ofName?_name] using congrArg ofName? same

/-- A name gives only the topic that has that name. -/
theorem name_of_ofName? {text : String} {topic : EventTopic}
    (found : ofName? text = some topic) : topic.name = text := by
  simpa using List.find?_some found

/-- Every topic is listed. -/
theorem mem_all (topic : EventTopic) : topic ∈ all := by
  cases topic <;> simp [all]

end EventTopic

/-- A name of a request is read as the topic with that name. -/
theorem readEventTopic_ok {text : String} {topic : EventTopic}
    (read : readEventTopic text = .ok topic) : topic.name = text := by
  unfold readEventTopic at read
  cases found : EventTopic.ofName? text with
  | none => simp [found] at read
  | some named =>
    simp only [found, Except.ok.injEq] at read
    subst read
    exact EventTopic.name_of_ofName? found

/-- A request is read as the topics whose names it lists, in order. -/
theorem readEventTopics_names {texts : List String} {topics : List EventTopic}
    (read : readEventTopics texts = .ok topics) : topics.map (·.name) = texts := by
  induction texts generalizing topics with
  | nil =>
    simp only [readEventTopics, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at read
    simp [← read]
  | cons text rest more =>
    obtain ⟨topic, others, first, later, rfl⟩ := Base.mapM_cons_ok.mp read
    simp [readEventTopic_ok first, more later]

/-- The names of some topics are read as those topics. -/
theorem readEventTopics_map_name (topics : List EventTopic) :
    readEventTopics (topics.map (·.name)) = .ok topics := by
  induction topics with
  | nil => rfl
  | cons topic rest more =>
    simp only [readEventTopics, List.map_cons] at more ⊢
    exact Base.mapM_cons_ok.mpr ⟨topic, rest, by simp [readEventTopic, EventTopic.ofName?_name],
      more, rfl⟩

/-- The stream of a list of events is the message of the first, if chosen, then the rest. -/
theorem eventStream_cons (write : Lean.Json → String) (topics : List EventTopic) (event : ApiEvent)
    (rest : List ApiEvent) :
    eventStream write topics (event :: rest) =
      (if event.subscribed topics then event.toStream write else "") ++
        eventStream write topics rest := by
  unfold eventStream
  cases chosen : event.subscribed topics <;> simp [chosen]

end EthLib.Consensus.BeaconApi
