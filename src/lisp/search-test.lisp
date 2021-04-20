(ql:quickload "shop3")

(in-package :shop-user)
(shop-trace :all)
(defdomain (good-test-domain :type pddl-domain :redefine-ok T) (
  (:types
    agent
  )

  (:predicates
   (test)
   (A-1 ?t - agent)
   (A-2 ?t - agent)
   (B-1 ?t - agent)
   (B-2 ?t - agent)
   (C-1 ?t - agent)
   (C-2 ?t - agent)
   (engineer ?t - agent)
   (medic ?t - agent)
  )

  (:action do-A-1
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (A-1 ?t)
  )

  (:action do-A-2
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (A-2 ?t)
  )

  (:action do-B-1
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (B-1 ?t)
  )

  (:action do-B-2
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (B-2 ?t)
  )

  (:action do-C-1
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (C-1 ?t)
  )

  (:action do-C-2
   :parameters (?t - agent)
   :precondition (engineer ?t)
   :effect (C-2 ?t)
  )

  (:method (complete-task)
    ()
    (:unordered (:task !do-A-1 ?t)
              (:task !do-A-2 ?t))
  )

  (:method (complete-task)
    ()
    (:unordered (:task !do-B-1 ?t)
              (:task !do-B-2 ?t))
  )

  (:method (complete-task)
    ()
    (:unordered (:task !do-C-1 ?t)
              (:task !do-C-2 ?t))
  )

))

(defproblem good-test-problem ((agent me) (agent you) (medic me) (engineer you) (test)) ((complete-task)))

(find-plans 'good-test-problem :which :all :verbose :long-plans)
