#!rlwrap python3.6
from lib.server import run_coq_server
from lib.top import Top

import sys
sys.setrecursionlimit(10000)

# initialize top loop
t = Top()
Top.set_default(t)

# first we start the holboost server to handle coq request
# the server works in background, but all the log messages will be displayed in foreground and
# the tasks will be rendered in the top's global
noserver = "-noserver" in sys.argv
profile = "-profile" in sys.argv

if not noserver:
    server = run_coq_server(top=t, profile=profile)
else:
    server = None

try:
    t.toploop()
except (KeyboardInterrupt, EOFError):
    print('toploop stopped.')
    t.store()
    if server is not None:
        server.shutdown()
