from http.server import BaseHTTPRequestHandler, HTTPServer
from formats.json import JsonFormat, JsonConvertError

import json

class CoqTaskHandler(BaseHTTPRequestHandler):

    def do_POST(self):

        reply = {
                "error" : True,
                "msg"   : "unhandled api url %s" % self.path
                }

        if self.path == "/prove":
            data = self.rfile.read(int(self.headers['content-length']))
            data = data.decode('utf8')

            try:
                print(JsonFormat.import_task(data))

                # do something ...
                reply = {
                        "error"    : False,
                        "finished" : True,
                        "msg"      : "",
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


def run_server(handler, port):
    print('start listening on port %d, press <Ctrl+c> to stop.' % port)
    try:
        http = HTTPServer(('', port), handler)
        http.serve_forever()
    except KeyboardInterrupt:
        print('server stopped.')


def run_coq_server(port=8081):
    run_server(CoqTaskHandler, port)
