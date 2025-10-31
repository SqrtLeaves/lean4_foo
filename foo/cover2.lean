import foo.topology

open NS_Topology

class Group

class Cover where
  source: TopoSpace ABS
  target: TopoSpace ABS
  map: TopoMap source target

class CoverMap where
  source_cover: Cover
  target_cover: Cover
  map: TopoMap source_cover.source target_cover.source

def is_connected_cover (c: Cover) : Prop := is_connected c.source

def is_galois_cover (c: Cover) : Prop := sorry

def even_act (G: Group) (Y: TopoSpace ABS) : Prop := sorry

def AutCover (c: Cover) : Group := sorry

def quotient_cover (G: Group) (Y: TopoSpace ABS) (_: even_act G Y) : Cover := sorry

theorem quotient_cover_to_galois (G: Group) (Y: TopoSpace ABS) (h: even_act G Y) (_:is_connected Y) :
  is_galois_cover (quotient_cover G Y h) := sorry

theorem connected_cover_to_even_act (c: Cover) (_:is_connected c.source) :
  even_act (AutCover c) c.source := sorry

theorem connected_even_act_to_cover (c: Cover) (G: Group) (_: even_act G c.source) :
  G = AutCover ()
