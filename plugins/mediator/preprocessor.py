def preprocess(grammar):
    lines = grammar.split("\n")
    counter = {}
    new_lines = []

    current_priority_rule = None
    last_priority_begins_at = -1

    def replace_previous_block(right_assoc=False):
        # default setting is left assoc
        # find some way to make it right assoc
        nonlocal new_lines

        if counter[current_priority_rule] == 0:
            current_level = current_priority_rule
        else:
            current_level = "%s%d" % (current_priority_rule, counter[current_priority_rule])

        next_level = "%s%d" % (current_priority_rule, counter[current_priority_rule] + 1)
        for j in range(last_priority_begins_at, len(new_lines)):
            if new_lines[j].strip().endswith("<precedence reset>"):
                new_lines[j] = new_lines[j].replace("<precedence reset>", "")
            else:
                new_lines[j] = new_lines[j].replace(
                        "%s " % current_priority_rule,
                        current_level + "_", 1
                        )
                new_lines[j] = new_lines[j].replace(
                        "%s " % current_priority_rule,
                        next_level + " "
                        )
                new_lines[j] = new_lines[j].replace(
                        current_level + "_",
                        current_level + " "
                        )

    for i in range(len(lines)):
        line = lines[i].strip()
        if line.startswith("---"):
            assert line.startswith("--- precedence") or line == "---", "invalid precedence macro"

            if line == "---":
                # the rule of precedence levels is already declared
                if current_priority_rule is None:
                    raise Exception("precedence macro is invoked before rule-name declared")
                else:
                    # replace
                    replace_previous_block()

                    # creating a rule reference for the next precedence level
                    # e.g.
                    #
                    #   expr : ....
                    #   ->
                    #   expr : ...
                    #       | expr1 -> atomic
                    #
                    #   expr1 : ...

                    next_level = "%s%d" % (current_priority_rule, counter[current_priority_rule] + 1)
                    new_lines.append("    | %s -> atomic" % (next_level))
                    # an empty line
                    new_lines.append("")
                    # generating declaration for the next precedence level
                    new_lines.append(next_level + ":")

                    counter[current_priority_rule] += 1
                    last_priority_begins_at = len(new_lines)
            else:
                rule_name = line[14:].strip()
                if rule_name == "end":
                    replace_previous_block()
                    current_priority_rule = None
                else:
                    counter[rule_name] = 0
                    current_priority_rule = rule_name
                    last_priority_begins_at = len(new_lines)
        else:
            new_lines.append(lines[i])

    return "\n".join(new_lines)


