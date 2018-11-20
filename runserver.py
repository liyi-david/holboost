#!rlwrap python3
from lib.server import run_coq_server
from lib.top import Top

import sys
sys.setrecursionlimit(100000)

t = Top()
Top.set_default(t)

# first we start the holboost server to handle coq request
# the server works in background, but all the log messages will be displayed in foreground and
# the tasks will be rendered in the top's global
noserver = "-noserver" in sys.argv

if not noserver:
    server = run_coq_server(top=t)
else:
    server = None

try:
    t.toploop()
except (KeyboardInterrupt, EOFError):
    print('toploop stopped.')
    t.store()
    if server is not None:
        server.shutdown()
