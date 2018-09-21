from http.server import BaseHTTPRequestHandler, HTTPServer
from interaction.formats.json import JsonFormat, JsonConvertError

import threading
import json


def CoqTaskHandlerFactory(top : 'Top'):
    # to generate CoqTaskHandlers with arguments

    class CoqTaskHandler(BaseHTTPRequestHandler):

        def do_POST(self):

            reply = {
                    "error" : True,
                    "msg"   : "unhandled api url %s" % self.path
                    }

            if self.path == "/prove":
                data = self.rfile.read(int(self.headers['content-length']))
                data = data.decode('utf8')
                top.namespace['debug'] = json.loads(data)

                try:
                    task = JsonFormat.import_task(data)
                    top.namespace['task'] = task

                    result = task.command.run(top)
                    top.print(JsonFormat.export_term(result))

                    reply = {
                            "error"    : False,
                            "finished" : True,
                            "msg"      : "",
                            "feedback" : JsonFormat.export_term(result, as_dict=True)
                            }

                except json.JSONDecodeError as err:
                    print(data[err.pos - 10:err.pos + 10])
                    reply = {
                            "error"    : True,
                            "msg"      : "json decoding failes because %s. for further information please refer to the server log" % str(err)
                            }
                except JsonConvertError as err:
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

