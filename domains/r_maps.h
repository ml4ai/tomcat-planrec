#pragma once

#include "typedefs.h"

Reach_Map transport_reach_map = {{"deliver",{"drive","noop","pick_up","drop"}},
                                 {"get_to",{"drive","noop"}},
                                 {"load",{"pick_up"}},
                                 {"unload",{"drop"}},
                                 {"m_deliver_ordering_0",{"drive","noop","pick_up","drop"}},
                                 {"m_unload_ordering_0",{"drop"}},
                                 {"m_load_ordering_0",{"pick_up"}},
                                 {"m_drive_to_ordering_0",{"drive"}},
                                 {"m_drive_to_via_ordering_0",{"drive"}},
                                 {"m_i_am_there_ordering_0", {"noop"}},
                                 {"drive",{"drive"}},
                                 {"noop",{"noop"}},
                                 {"pick_up",{"pick_up"}},
                                 {"drop",{"drop"}}
                                };

Reach_Maps reach_maps = {{"transport_reach_map",transport_reach_map}};
