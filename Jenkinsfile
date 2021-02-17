/*      Change this list with your baranch names if you want build it.
        For example:
def BUILD_IF_BRANCH = ['master','develop']  */

def BUILD_IF_BRANCH = ['feature/int_correctness']

pipeline {
    agent { 
        dockerfile {
               filename 'Dockerfile'
               label 'DOCKER_HOST' 
               args '-u root:sudo --privileged'
        }
    }

    stages {
		stage('Prepare') {
			steps {
				script {
					env.GIT_COMMIT_MSG = sh (script: 'git log -1 --pretty=%B ${GIT_COMMIT}', returnStdout: true).trim()
					env.GIT_AUTHOR = sh (script: 'git log -1 --pretty=%cn ${GIT_COMMIT}', returnStdout: true).trim()
					skip_ci_result = sh (script: "git log -1 | grep '.*\\[skip ci\\].*'", returnStatus: true)
					if (skip_ci_result == 0) {
						env.SKIP_CI = "true"
						echo "Build going to be skiped due to [skip ci] tag"
					}
					if (env.BRANCH_NAME in BUILD_IF_BRANCH) {
						env.SKIP_BRANCH = "false"
					} else {
						env.SKIP_BRANCH = "true"
						echo "Build going to be skiped due to branche name"
					  }
				}
			}
		}
		
        stage('Build') {
			steps {
				script {
					if (env.SKIP_CI != "true" && env.SKIP_BRANCH == "false") {
						sh '''
						    eval `ssh-agent`
                            eval $(opam env)
		                    export WORKDIR=`pwd`
                            cd ..
                            git clone https://${BITBUCKET_CREDS}@bitbucket.org/codeminders/asn1c.git
		                    cd asn1c
		                    git fetch -a
                            git checkout vst_modifications
		                    cd $WORKDIR/src
                            make clight
                            make
						  '''
					}
				}
			}
		}
    }
    
	post {
        always {
	       /* Use slackNotifier.groovy from shared library and provide current build result as parameter */
           notifySlack(currentBuild.result)
           cleanWs()
        }
    }
}

/*   Functions   */
/* ----------------------------------------------------------------------------------------------------  */

def notifySlack(String buildStatus = 'STARTED') {
    // Build status of null means success.
    buildStatus = buildStatus ?: 'SUCCESS'

    def color

    if (buildStatus == 'STARTED') {
        color = '#D4DADF'
    } else if (buildStatus == 'SUCCESS') {
        color = '#BDFFC3'
    } else if (buildStatus == 'UNSTABLE') {
        color = '#FFFE89'
    } else {
        color = '#FF9FA1'
    }

    def msg = "Build <${env.BUILD_URL}|#${env.BUILD_NUMBER}> (${getSlackRepoURL()}) of ${env.JOB_NAME} (${env.GIT_BRANCH}) by ${env.GIT_AUTHOR} ${buildStatus} in ${currentBuild.durationString.minus(' and counting')}"

	if (env.SKIP_BRANCH == "false" && !(env.SKIP_CI == "true")) {
		slackSend(color: color, message: msg, channel: '#bitbucket-activity')
    }
}

def getRepoURL() {
	sh "git config --get remote.origin.url > .git/remote-url"
	return readFile(".git/remote-url").trim()
}

def getRepoSHA() {
	sh "git rev-parse HEAD > .git/current-commit"
	return readFile(".git/current-commit").trim()
}

def getSlackRepoURL() {
	repoURL = getRepoURL()
	repoURL = repoURL.take(repoURL.length()-4) + "/commit"
	repoSHA = getRepoSHA()
	 
	return "<${repoURL}/${repoSHA}|${getRepoSHA().take(7)}>"
}
