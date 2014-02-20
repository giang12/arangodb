# coding: utf-8

require 'rspec'
require 'arangodb.rb'

describe ArangoDB do
  prefix = "rest-create-document"
  didRegex = /^([0-9a-zA-Z]+)\/([0-9a-zA-Z\-_]+)/

  context "creating a document:" do

################################################################################
## error handling
################################################################################

    context "error handling:" do
      it "returns an error if url contains a suffix" do
        cmd = "/_api/document/123456"
        body = "{}"
        doc = ArangoDB.log_post("#{prefix}-superfluous-suffix", cmd, :body => body)

        doc.code.should eq(400)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(601)
        doc.parsed_response['code'].should eq(400)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
      end

      it "returns an error if collection idenifier is missing" do
        cmd = "/_api/document"
        body = "{}"
        doc = ArangoDB.log_post("#{prefix}-missing-cid", cmd, :body => body)

        doc.code.should eq(400)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(1204)
        doc.parsed_response['code'].should eq(400)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
      end

      it "returns an error if the collection identifier is unknown" do
        cmd = "/_api/document?collection=123456"
        body = "{}"
        doc = ArangoDB.log_post("#{prefix}-unknown-cid", cmd, :body => body)

        doc.code.should eq(404)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(1203)
        doc.parsed_response['code'].should eq(404)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
      end

      it "returns an error if the collection name is unknown" do
        cmd = "/_api/document?collection=unknown_collection"
        body = "{}"
        doc = ArangoDB.log_post("#{prefix}-unknown-name", cmd, :body => body)

        doc.code.should eq(404)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(1203)
        doc.parsed_response['code'].should eq(404)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
      end

      it "returns an error if the JSON body is corrupted" do
        cn = "UnitTestsCollectionBasics"
        id = ArangoDB.create_collection(cn)

        id.should be_kind_of(String)

        cmd = "/_api/document?collection=#{id}"
        body = "{ 1 : 2 }"
        doc = ArangoDB.log_post("#{prefix}-bad-json", cmd, :body => body)

        doc.code.should eq(400)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(600)
        doc.parsed_response['code'].should eq(400)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")

        ArangoDB.size_collection(cn).should eq(0)

        ArangoDB.drop_collection(cn)
      end
    end

################################################################################
## known collection identifier, waitForSync = true
################################################################################

    context "known collection identifier, waitForSync = true:" do
      before do
        @cn = "UnitTestsCollectionBasics"
        @cid = ArangoDB.create_collection(@cn)
      end

      after do
        ArangoDB.drop_collection(@cn)
      end

      it "creating a new document" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document complex body" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"Wo\\\"rld\" }"
        doc = ArangoDB.log_post("#{prefix}", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-complex", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['Hallo'].should eq('Wo"rld')

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document complex body, setting compatibility header " do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"Wo\\\"rld\" }"
        doc = ArangoDB.log_post("#{prefix}", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-complex", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['Hallo'].should eq('Wo"rld')

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end

      it "creating a new umlaut document" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"öäüÖÄÜßあ寿司\" }"
        doc = ArangoDB.log_post("#{prefix}-umlaut", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-umlaut", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")

        newBody = doc.body()
        newBody = newBody.sub!(/^.*"Hallo":"([^"]*)".*$/, '\1')

        newBody.should eq("\\u00F6\\u00E4\\u00FC\\u00D6\\u00C4\\u00DC\\u00DF\\u3042\\u5BFF\\u53F8")

        doc.parsed_response['Hallo'].should eq('öäüÖÄÜßあ寿司')
        
        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new umlaut document, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"öäüÖÄÜßあ寿司\" }"
        doc = ArangoDB.log_post("#{prefix}-umlaut", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-umlaut", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")

        newBody = doc.body()
        newBody = newBody.sub!(/^.*"Hallo":"([^"]*)".*$/, '\1')

        newBody.should eq("\\u00F6\\u00E4\\u00FC\\u00D6\\u00C4\\u00DC\\u00DF\\u3042\\u5BFF\\u53F8")

        doc.parsed_response['Hallo'].should eq('öäüÖÄÜßあ寿司')
        
        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end

      it "creating a new not normalized umlaut document" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"Gru\\u0308\\u00DF Gott.\" }"
        doc = ArangoDB.log_post("#{prefix}-umlaut", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)

        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-umlaut", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")

        newBody = doc.body()
        newBody = newBody.sub!(/^.*"Hallo":"([^"]*)".*$/, '\1')

        newBody.should eq("Gr\\u00FC\\u00DF Gott.")

        doc.parsed_response['Hallo'].should eq('Grüß Gott.')

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new not normalized umlaut document, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"Gru\\u0308\\u00DF Gott.\" }"
        doc = ArangoDB.log_post("#{prefix}-umlaut", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)

        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        cmd = "/_api/document/#{did}"
        doc = ArangoDB.log_get("#{prefix}-umlaut", cmd)

        doc.code.should eq(200)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")

        newBody = doc.body()
        newBody = newBody.sub!(/^.*"Hallo":"([^"]*)".*$/, '\1')

        newBody.should eq("Gr\\u00FC\\u00DF Gott.")

        doc.parsed_response['Hallo'].should eq('Grüß Gott.')

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end

      it "creating a document with an existing id" do
        @key = "a_new_key"

        ArangoDB.delete("/_api/document/#{@cn}/#{@key}")

        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"some stuff\" : \"goes here\", \"_key\" : \"#{@key}\" }"
        doc = ArangoDB.log_post("#{prefix}-existing-id", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        did.should eq("#{@cn}/#{@key}")
  
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        location.should eq("/_api/document/#{did}")

        ArangoDB.delete("/_api/document/#{@cn}/#{@key}")
      end
      
      it "creating a document with an existing id, setting compatibility header" do
        @key = "a_new_key"

        ArangoDB.delete("/_api/document/#{@cn}/#{@key}")

        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"some stuff\" : \"goes here\", \"_key\" : \"#{@key}\" }"
        doc = ArangoDB.log_post("#{prefix}-existing-id", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        did.should eq("#{@cn}/#{@key}")
  
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete("/_api/document/#{@cn}/#{@key}")
      end
      
      it "creating a document with a duplicate existing id" do
        @key = "a_new_key"

        ArangoDB.delete("/_api/document/#{@cn}/#{@key}")

        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"some stuff\" : \"goes here\", \"_key\" : \"#{@key}\" }"
        doc = ArangoDB.log_post("#{prefix}-existing-id", cmd, :body => body)

        doc.code.should eq(201)

        # send again
        doc = ArangoDB.log_post("#{prefix}-existing-id", cmd, :body => body)
        doc.code.should eq(409) # conflict
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['code'].should eq(409)
        doc.parsed_response['errorNum'].should eq(1210)

        ArangoDB.delete("/_api/document/#{@cn}/#{@did}")
      end
    end

################################################################################
## known collection identifier, waitForSync = false
################################################################################

    context "known collection identifier, waitForSync = false:" do
      before do
        @cn = "UnitTestsCollectionUnsynced"
        @cid = ArangoDB.create_collection(@cn, false)
      end

      after do
        ArangoDB.drop_collection(@cn)
      end

      it "creating a new document" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(202)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(202)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, waitForSync URL param = false" do
        cmd = "/_api/document?collection=#{@cn}&waitForSync=false"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept-sync-false", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(202)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, waitForSync URL param = false, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}&waitForSync=false"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept-sync-false", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(202)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, waitForSync URL param = true" do
        cmd = "/_api/document?collection=#{@cn}&waitForSync=true"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept-sync-true", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
      
      it "creating a new document, waitForSync URL param = true, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}&waitForSync=true"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-accept-sync-true", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
    end

################################################################################
## known collection name
################################################################################

    context "known collection name:" do
      before do
        @cn = "UnitTestsCollectionBasics"
        @cid = ArangoDB.create_collection(@cn)
      end

      after do
        ArangoDB.drop_collection(@cn)
      end
      
      it "creating a new document" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-named-collection", cmd, :body => body, :headers => { "x-arango-version" => "1.3" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end

      it "creating a new document, setting compatibility header" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-named-collection", cmd, :body => body, :headers => { "x-arango-version" => "1.4" })

        doc.code.should eq(201)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
        doc.parsed_response['error'].should eq(false)

        etag = doc.headers['etag']
        etag.should be_kind_of(String)

        location = doc.headers['location']
        location.should be_kind_of(String)

        rev = doc.parsed_response['_rev']
        rev.should be_kind_of(String)

        did = doc.parsed_response['_id']
        did.should be_kind_of(String)
        
        match = didRegex.match(did)

        match[1].should eq("#{@cn}")

        etag.should eq("\"#{rev}\"")
        location.should eq("/_db/_system/_api/document/#{did}")

        ArangoDB.delete(location)

        ArangoDB.size_collection(@cn).should eq(0)
      end
    end

################################################################################
## unknown collection name
################################################################################

    context "unknown collection name:" do
      before do
        @cn = "UnitTestsCollectionNamed#{Time.now.to_i}"
      end

      after do
        ArangoDB.drop_collection(@cn)
      end

      it "returns an error if collection is unknown" do
        cmd = "/_api/document?collection=#{@cn}"
        body = "{ \"Hallo\" : \"World\" }"
        doc = ArangoDB.log_post("#{prefix}-create-collection", cmd, :body => body)

        doc.code.should eq(404)
        doc.parsed_response['error'].should eq(true)
        doc.parsed_response['errorNum'].should eq(1203)
        doc.parsed_response['code'].should eq(404)
        doc.headers['content-type'].should eq("application/json; charset=utf-8")
      end
      
    end

  end
end
