from http.server import BaseHTTPRequestHandler, HTTPServer
from interaction.formats.json import JsonFormat, JsonConvertError

from kernel.environment import NamedEnvironment

import threading
import json


def CoqTaskHandlerFactory(top : 'Top'):
    # to generate CoqTaskHandlers with arguments

    class CoqTaskHandler(BaseHTTPRequestHandler):

        def do_POST(self):

            data = self.rfile.read(int(self.headers['content-length']))
            data = data.decode('utf8')
            parsed_data = json.loads(data)

            top.namespace['req'] = data

            reply = {
                    "error" : True,
                    "msg"   : "unhandled api url %s" % self.path
                    }

            if self.path == "/coq":

                try:
                    task = JsonFormat.import_task(parsed_data['content'])
                    task.client = parsed_data['client']
                    task.client_addr = self.client_address

                    top.print(task)

                    # merge buffered builtin declarations with the task
                    if task.client in top.namespace['cache']:
                        task.inherited_environment = top.namespace['cache'][task.client]

                    top.namespace['__task__'] = task

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

                    top.debug("server", "response", reply)

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
                    top.print(str(err))
                    reply = {
                            "error"    : True,
                            "msg"      : str(err)
                            }


            self.send_response(200)
            self.send_header('Content-type', 'text/json')
            self.end_headers()
            self.wfile.write(json.dumps(reply).encode('utf8'))


        def log_message(self, format, *args):
            top.log_message(format % args)

    return CoqTaskHandler



def run_coq_server(port=8081, top=None):
    print('start listening on port %d, press <Ctrl+c> to stop.' % port)
    http = HTTPServer(('', port), CoqTaskHandlerFactory(top))
    thread = threading.Thread(target = http.serve_forever)
    thread.daemon = True
    thread.start()
    return http

