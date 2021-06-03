; Example domain for testing

(define 
    (domain construction)
    (:requirements :strips :typing)
    (:types site bricks)
    (:constants mainsite - site)
    (:predicates
        (walls-built ?s - site)
        (windows-fitted ?s - site)
        (foundations-set ?s - site)
        (cables-installed ?s - site)
        (site-built ?s - site)
        (on-site ?m - material ?s - site)
        (material-used ?m - material))
    (:action build-wall 
     :parameters (?s - site ?b - bricks)))
