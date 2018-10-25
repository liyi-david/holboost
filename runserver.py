#!rlwrap python3
from lib.server import run_coq_server
from lib.top import Top

import sys
sys.setrecursionlimit(100000)

t = Top()

# first we start the holboost server to handle coq request
# the server works in background, but all the log messages will be displayed in foreground and
# the tasks will be rendered in the top's global
server = run_coq_server(top=t)
try:
    t.toploop()
except (KeyboardInterrupt, EOFError):
    print('toploop stopped.')
    server.shutdown()
