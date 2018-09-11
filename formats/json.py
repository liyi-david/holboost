from formats.format import Format
from kernel.term import *
import json


class JsonConvertError(Exception):
    pass


class JsonFormat(Format):

    @staticmethod
    def import_term (external_t):
        # external term should be described by json string
        assert isinstance(external_t, str)
        json_item = json.loads(external_t)

        def convert(t):
            if t['type'] is 'sort':
                sort_map = { 'type' : TYPE, 'set' : SET, 'prop' : PROP }
                if t['sort'] not in sort_map:
                    raise JsonConvertError('invalid sort name %s' % t['sort'])
                return sort_map[t['sort']]
            else:
                raise JsonConvertError('unhandled json node %s' % json.dumps(t))

        return convert(json_item)

