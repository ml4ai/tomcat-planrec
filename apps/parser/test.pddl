; Example domain for testing

(define 
  (domain construction)
  (:requirements :strips :typing)
  (:types site bricks)
  (:action build-wall 
   :parameters (?s - site ?b - bricks)))
