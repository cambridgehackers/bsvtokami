//
// Created by Jamey Hicks on 11/11/19.
//

#ifndef BSV_PARSER_PATTERN_H
#define BSV_PARSER_PATTERN_H

#include <memory>
#include <iostream>
#include <string>
#include <vector>

using namespace std;

enum PatternType {
    InvalidPatternType,
    IntPatternType,
    TaggedPatternType,
    TuplePatternType,
    VarPatternType,
    WildcardPatternType
};
class IntPattern;
class TaggedPattern;
class TuplePattern;
class VarPattern;
class WildcardPattern;

class Pattern: public enable_shared_from_this<Pattern>  {
public:
    PatternType patternType;

    Pattern(PatternType patternType) : patternType(patternType) {}
    virtual ~Pattern() {}

    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) = 0;
    virtual shared_ptr<IntPattern> intPattern() { return shared_ptr<IntPattern>(); }
    virtual shared_ptr<TaggedPattern> taggedPattern() { return shared_ptr<TaggedPattern>(); }
    virtual shared_ptr<TuplePattern> tuplePattern() { return shared_ptr<TuplePattern>(); }
    virtual shared_ptr<VarPattern> varPattern() { return shared_ptr<VarPattern>(); }
    virtual shared_ptr<WildcardPattern> wildcardPattern() { return shared_ptr<WildcardPattern>(); }
};

class IntPattern : public Pattern {
public:
    const int value;
    IntPattern(int value) : Pattern(IntPatternType), value(value) {}
    IntPattern(const string &value) : Pattern(IntPatternType), value(stol(value, 0, 0)) {}

    ~IntPattern() {}

    virtual shared_ptr<IntPattern> intPattern() override { return static_pointer_cast<IntPattern, Pattern>(shared_from_this()); }
    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) override;
    static shared_ptr<IntPattern> create(int value) { return shared_ptr<IntPattern>(new IntPattern(value)); }
};

class TaggedPattern : public Pattern {
public:
    const string value;
    const shared_ptr<Pattern> pattern;
    //FIXME struct patterns

    TaggedPattern(const string &value) : Pattern(TaggedPatternType), value(value) {}

    TaggedPattern(const string &value, const shared_ptr<Pattern> &pattern) : Pattern(TaggedPatternType), value(value),
                                                                             pattern(pattern) {}

    ~TaggedPattern() {}

    virtual shared_ptr<TaggedPattern> taggedPattern() override {
        return static_pointer_cast<TaggedPattern, Pattern>(shared_from_this());
    }

    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) override;
    static shared_ptr<TaggedPattern> create(const string &value) { return shared_ptr<TaggedPattern>(new TaggedPattern(value)); }
};

class TuplePattern : public Pattern {
public:
    const vector<shared_ptr<Pattern>> subpatterns;
    TuplePattern(const vector<shared_ptr<Pattern>> &subpatterns) : Pattern(TuplePatternType), subpatterns(subpatterns) {}
    ~TuplePattern() {}

    virtual shared_ptr<TuplePattern> tuplePattern() override { return static_pointer_cast<TuplePattern, Pattern>(shared_from_this()); }
    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) override;
    static shared_ptr<TuplePattern> create(const vector<shared_ptr<Pattern>> &subpatterns) { return shared_ptr<TuplePattern>(new TuplePattern(subpatterns)); }

};

class VarPattern : public Pattern {
public:
    const string value;
    VarPattern(const string &value) : Pattern(VarPatternType), value(value) {}
    ~VarPattern() {}

    virtual shared_ptr<VarPattern> varPattern() override { return static_pointer_cast<VarPattern, Pattern>(shared_from_this()); }
    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) override;
    static shared_ptr<VarPattern> create(const string &value) { return shared_ptr<VarPattern>(new VarPattern(value)); }
};

class WildcardPattern : public Pattern {
public:
    WildcardPattern() : Pattern(WildcardPatternType) {}
    ~WildcardPattern() {}

    virtual shared_ptr<WildcardPattern> wildcardPattern() override { return static_pointer_cast<WildcardPattern, Pattern>(shared_from_this()); }
    virtual void prettyPrint(ostream &out, int depth = 0, int precedence = 0) override;
    static shared_ptr<WildcardPattern> create() { return shared_ptr<WildcardPattern>(new WildcardPattern()); }

};


#endif //BSV_PARSER_PATTERN_H
