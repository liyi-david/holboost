from formats.format import Format
from kernel.term import *
from kernel.task import Task
import json


class JsonConvertError(Exception):
    pass


class JsonFormat(Format):

    @staticmethod
    def import_term (external_t):
        # external term should be described by json string
        if isinstance(external_t, str):
            json_item = json.loads(external_t)
        else:
            json_item = external_t

        def convert(t):
            if t['type'] == 'sort':
                sort_map = { 'type' : TYPE, 'set' : SET, 'prop' : PROP }
                if t['sort'] not in sort_map:
                    raise JsonConvertError('invalid sort name %s' % t['sort'])
                return sort_map[t['sort']]
            elif t['type'] == 'app':
                args = list(map(convert, t['args']))
                return Apply(convert(t['func']), *args)
            elif t['type'] == 'const':
                return Const(t['name'])
            elif t['type'] == 'construct':
                return Construct(t['mutind_name'], t['ind_index'], t['constructor_index'])
            elif t['type'] == 'lambda':
                return Lambda(t['arg_name'], convert(t['arg_type']), convert(t['body']))
            elif t['type'] == 'ind':
                return Ind(t['mutind_name'], t['ind_index'])
            elif t['type'] == 'var':
                return Var(t['name'])
            elif t['type'] == 'rel':
                return Rel(t['index'])
            else:
                raise JsonConvertError('unhandled json node %s' % json.dumps(t))

        return convert(json_item)

    @staticmethod
    def import_task(external_t):
        # external term should be described by json string
        if isinstance(external_t, str):
            json_item = json.loads(external_t)
        else:
            json_item = external_t

        return Task(JsonFormat.import_term(json_item['goal']))

