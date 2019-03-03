from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs
from time import time
from sys import stdout

from interaction.formats.json import JsonFormat, JsonConvertError
from kernel.environment import NamedEnvironment

import threading
import traceback
import cProfile

import json

def CoqTaskHandlerFactory(top : 'Top', profile : bool):
    # to generate CoqTaskHandlers with arguments

    class CoqTaskHandler(BaseHTTPRequestHandler):

        total_handled_tasks = 0
        total_time_cost = 0

        def do_POST(self):

            t0 = time()

            if self.client_address[0] in ('localhost', '127.0.0.1'):
                # when the request comes from localhost, we perfer reading the task
                # from a file on the disk
                tmp_filename = self.path[1:]
                with open(tmp_filename, 'rb') as f:
                    data = f.read()
            else:
                # FIXME rfile.read could be extremely slow due to a signal-waiting issue
                # this is still not clear for me, but currently we only consider local
                # requests
                data = self.rfile.read(int(self.headers['content-length']))

            top.debug("server", "data reading time cost: %.6f" % (time() - t0))

            t1 = time()

            data = data.decode('utf8')
            parsed_data = json.loads(data)

            top.debug("server", "posted data size %d" % len(data))
            top.debug("server", "data pre-processing time cost: %.6f" % (time() - t1))


            top.namespace['__request__'] = parsed_data

            reply = {
                    "error" : True,
                    "msg"   : "unhandled api url %s" % self.path
                    }

            try:
                t1 = time()
                task = JsonFormat.import_task(parsed_data['content'])
                top.debug("server", "task importing time cost: %.6f" % (time() - t1))
                task.client = parsed_data['client']
                task.client_addr = self.client_address

                top.print(task)

                # merge buffered builtin declarations with the task
                if task.client in top.namespace['cache']:
                    task.inherited_environment = top.namespace['cache'][task.client]

                top.namespace['__task__'] = task

                if profile:
                    prof = cProfile.Profile()
                    result = prof.runcall(task.run, top)
                    prof.dump_stats("profile.out")
                else:
                    result = task.run(top)

                top.namespace['__result__'] = result

                if task.client not in top.namespace['cache']:
                    builtins = task.get_builtins()
                    if len(builtins.constants().values()) + len(builtins.mutinds().values()) > 0:
                        top.namespace['cache'][task.client] = builtins

                reply = {
                        "error"    : False,
                        "finished" : True,
                        "msg"      : "",
                        "feedback" : result,
                        "builtin_cached": (task.client in top.namespace['cache']),
                        }

                # top.debug("server", "response", reply)

            except json.JSONDecodeError as err:
                top.print(data[err.pos - 10:err.pos + 10])
                reply = {
                        "error"    : True,
                        "msg"      : "json decoding failes because %s. for further information please refer to the server log" % str(err)
                        }
            except JsonConvertError as err:
                top.print(str(err))
                reply = {
                        "error"    : True,
                        "msg"      : str(err)
                        }
            except Exception as err:
                traceback.print_exc()

                reply = {
                        "error"    : True,
                        "msg"      : str(err)
                        }


            self.send_response(200)
            self.send_header('Content-type', 'text/json')
            self.end_headers()

            t = time()
            self.wfile.write(json.dumps(reply).encode('utf8'))

            time_cost = time() - t0
            json_time_cost = time() - t
            self.total_time_cost += time_cost
            self.total_handled_tasks += 1

            top.debug("server", "json encoding time cost : %.6f" % json_time_cost)
            top.debug("server", "task time cost : %.6f" % time_cost)
            top.debug("server", "average task time cost : %.6f" % (self.total_time_cost / self.total_handled_tasks))


        def log_message(self, format, *args):
            top.log_message(format % args)

    return CoqTaskHandler



def run_coq_server(port=8081, top=None, profile=False):
    print('start listening on port %d, press <Ctrl+c> to stop.' % port)
    http = HTTPServer(('', port), CoqTaskHandlerFactory(top, profile))
    thread = threading.Thread(target = http.serve_forever)
    thread.daemon = True
    thread.start()
    return http

